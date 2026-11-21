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


def group_key(parent, modules):
    return digest(["lean-module-group/v1", parent, *modules])


def published_groups(data, index, edges):
    for number, shard in enumerate(data["shards"]):
        if parts.asset_name(shard["key"]) in index:
            continue
        for group_id, modules in enumerate(module_groups(shard["modules"], edges)):
            name = parts.asset_name(group_key(shard["key"], modules))
            if name in index:
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
        for i, modules in enumerate(module_groups(shard["modules"], edges)):
            key = group_key(shard["key"], modules)
            imports = {dep for module in modules for dep in edges[module]} - set(modules)
            if parts.asset_name(key) not in index and imports <= available:
                result.append({"number": number, "group": i, "key": key})
    return result


def reuse(data, number, edges, repo):
    shard = data["shards"][number]
    # The parent may have waited on the group workflow's concurrency lock after planning.
    index = parts.inventory(repo)
    found = []
    for i, modules in enumerate(module_groups(shard["modules"], edges)):
        name = parts.asset_name(group_key(shard["key"], modules))
        if name in index:
            found.append((i, name, set(modules)))
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
        modules = module_groups(shard["modules"], edges)[int(group)]
        if key != group_key(shard["key"], modules):
            raise ValueError("Group key does not match the source plan")
        imports = {dep for m in modules for dep in edges[m]} - set(modules)
        install_partial_imports(data, index, imports, edges)
        data["shards"][number] = dict(shard, modules=modules, key=key)
        parts.build(data, index, number)
    else:
        raise ValueError(command)


if __name__ == "__main__":
    main()
