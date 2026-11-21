"""Compile connected groups with released imports and reuse them in their parent shard."""
import gzip
import json
import os
import sys

import parts
from plan import digest, graph


def module_groups(modules, edges):
    local = set(modules)
    groups = []
    for module in modules:
        joined = {module} | (set(edges[module]) & local)
        for other in [group for group in groups if group & joined]:
            groups.remove(other)
            joined.update(other)
        groups.append(joined)
    return sorted(sorted(group) for group in groups)


def build_groups(modules, edges):
    groups = module_groups(modules, edges)
    # Existing connected groups retain their IDs. Individual modules can run when
    # a different import of the same connected group is still missing.
    return groups + [[m] for group in groups if len(group) > 1 for m in group]


def group_key(parent, modules):
    return digest(["lean-module-group/v1", parent, *modules])


def assembly_inputs(shards, numbers):
    """Map opted-in shards to the archives required to restore every target."""
    enabled = set(json.loads(os.environ.get("RH_GROUP_SHARDS") or "[]")).intersection(numbers)
    if not enabled:
        return {}
    _, edges = graph()
    inputs = {}
    for number in enabled:
        shard = shards[number]
        inputs[number] = {parts.asset_name(group_key(shard["key"], modules))
                          for modules in module_groups(shard["modules"], edges)}
    return inputs


def complete_assemblies(inputs, index):
    return {number for number, names in inputs.items() if names and names.issubset(index)}


def shard_archives(shard, index, edges):
    covered = set()
    for group_id, modules in enumerate(build_groups(shard["modules"], edges)):
        if covered.issuperset(modules):
            continue
        name = parts.asset_name(group_key(shard["key"], modules))
        if name in index:
            covered.update(modules)
            yield group_id, name, set(modules)


def published_groups(data, index, edges):
    for number, shard in enumerate(data["shards"]):
        if parts.asset_name(shard["key"]) not in index:
            for group_id, name, modules in shard_archives(shard, index, edges):
                yield number, group_id, name, modules


def install_partial_imports(data, index, imports, edges):
    wanted = parts.dependencies(imports, edges)
    for number, group_id, name, modules in published_groups(data, index, edges):
        overlap = wanted.intersection(modules)
        if not overlap:
            continue
        marker = parts.receipt(data["shards"][number]["key"])
        installed = set(marker.read_text().splitlines()) if marker.exists() else set()
        outputs = {m: parts.BUILD / "lib/lean" / (m.replace(".", "/") + ".olean") for m in overlap}
        needed = {m for m, path in outputs.items() if m not in installed or not path.is_file()}
        if not needed:
            continue
        parts.unpack(f"{number}-group-{group_id}", name, index[name], needed)
        if any(not outputs[m].is_file() for m in needed):
            raise ValueError(f"{name} did not restore all requested modules")
        # Record only installed modules; the canonical archive is still unpublished.
        marker.parent.mkdir(parents=True, exist_ok=True)
        marker.write_text("\n".join(sorted(installed | needed)))


def ready_groups(data, index, number, edges):
    shard = data["shards"][number]
    available = {module for part in data["shards"] if parts.asset_name(part["key"]) in index
                 for module in part["modules"]}
    for _, _, _, modules in published_groups(data, index, edges):
        available.update(modules)
    result = []
    if parts.asset_name(shard["key"]) not in index:
        claimed = set()
        for i, modules in enumerate(build_groups(shard["modules"], edges)):
            if claimed.issuperset(modules):
                continue
            key = group_key(shard["key"], modules)
            imports = {dep for module in modules for dep in edges[module]} - set(modules)
            if parts.asset_name(key) in index:
                claimed.update(modules)
            elif imports <= available:
                claimed.update(modules)
                result.append({"number": number, "group": i, "key": key})
    return result


def reuse(data, number, edges, repo):
    shard = data["shards"][number]
    # The parent may have waited on the group workflow's concurrency lock after planning.
    index = parts.inventory(repo)
    found = list(shard_archives(shard, index, edges))
    prebuilt = {m for _, _, modules in found for m in modules}
    if prebuilt:
        imports = {dep for m in prebuilt for dep in edges[m]} - prebuilt
        install_partial_imports(data, index, imports, edges)
        parts.restore(data, index, imports, edges)
        for i, name, modules in found:
            parts.unpack(f"{number}-group-{i}", name, index[name], modules)
        parts.lake(prebuilt, reuse=True)
    print(f"Shard {number}: reused {len(prebuilt)}/{len(shard['modules'])} modules from {len(found)} groups",
          flush=True)


def main():
    command, raw_number, *args = sys.argv[1:]
    number = int(raw_number)
    repo = os.environ["GITHUB_REPOSITORY"]
    if command == "plan":
        parts.prepare(repo)
    with gzip.open(parts.PLAN) as file:
        data = json.load(file)
    assert data["head"] == parts.output("git", "rev-parse", "HEAD")
    shard = data["shards"][number]
    _, edges = graph()
    if command == "reuse":
        reuse(data, number, edges, repo)
        return
    index = json.loads(parts.INDEX.read_text())
    if command == "plan":
        if shard["key"] != args[0]:
            raise ValueError("Parent shard key does not match the source plan")
        selected = ready_groups(data, index, number, edges)
        with open(os.environ["GITHUB_OUTPUT"], "a") as file:
            print("matrix=" + json.dumps(selected), file=file)
    elif command == "build":
        group, key = args
        modules = build_groups(shard["modules"], edges)[int(group)]
        if key != group_key(shard["key"], modules):
            raise ValueError("Group key does not match the source plan")
        install_partial_imports(data, index, modules, edges)
        data["shards"][number] = dict(shard, modules=modules, key=key)
        parts.build(data, index, number)
    else:
        raise ValueError(command)


if __name__ == "__main__":
    main()
