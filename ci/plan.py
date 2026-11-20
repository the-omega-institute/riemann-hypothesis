"""Partition Main's import closure into bounded, dependency-ordered build jobs."""
import collections
import gzip
import hashlib
import json
import subprocess
import sys
from planning import split_graph

MAX_MODULES = 400
MAX_BYTES = 2_500_000


def git(*args):
    return subprocess.check_output(["git", "-c", "core.quotePath=false", *args])


def digest(parts):
    return hashlib.sha256("\0".join(parts).encode()).hexdigest()


def graph():
    files = {}
    for line in git("ls-tree", "-rl", "HEAD", "src").decode().splitlines():
        meta, path = line.split("\t", 1)
        if path.endswith(".lean"):
            mod = path[4:-5].replace("/", ".")
            files[mod] = (meta.split()[2], int(meta.split()[3]))
    deps = {mod: [] for mod in files}
    imports = git("grep", "--threads=4", "-E", r"^[[:space:]]*((public|private|meta) +)*import[[:space:]]", "HEAD", "--", "src").decode()
    for line in imports.splitlines():
        path, stmt = line.removeprefix("HEAD:").split(":", 1)
        module = path[4:-5].replace("/", ".")
        names = stmt.split("--")[0].split("import", 1)[1].split()
        for name in names:
            if name in files:
                deps[module].append(name)
            elif name.split(".")[0] in {"Development", "Formalism", "GroundTheory", "Supplements", "BuildAid", "Lemmata", "CompanionTheory", "PositivityTheory", "ReciprocityTheory"}:
                raise ValueError(f"{module}: missing import {name}")
    return files, deps


def plan():
    files, deps = graph()
    height = {}
    def visit(mod):
        if mod not in height:
            height[mod] = 1 + max((visit(d) for d in deps[mod]), default=-1)
        return height[mod]
    visit("Main")
    config = digest([git("rev-parse", "HEAD:" + p).decode().strip() for p in
                     ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]] + ["lake-leanArts/linux-x86_64/v1"])
    # Reconstruct the original sixteen foundation shards and bootstrap so releases
    # made by the first scheduler retain exactly the same content addresses.
    bootstrap = sorted(m for m in height if not deps[m] and (m == "Statements" or m.startswith("BuildAid.")))
    foundations = [{"stage": 0, "bytes": sum(files[m][1] for m in bootstrap), "modules": bootstrap, "deps": set()}]
    owner = dict.fromkeys(bootstrap, 0)
    for mod in sorted(height.keys() - owner.keys(), key=lambda m: (height[m], m)):
        size = files[mod][1]
        parents = {owner.get(d) for d in deps[mod]}
        if parents:
            if len(parents) != 1 or None in parents or 0 in parents:
                continue
            i = next(iter(parents))
        else:
            i = len(foundations) - 1
        shard = foundations[i]
        if i == 0 or len(shard["modules"]) >= MAX_MODULES or shard["bytes"] + size > MAX_BYTES:
            if parents:
                continue
            i = len(foundations)
            shard = {"stage": 0, "bytes": 0, "modules": [], "deps": set()}
            foundations.append(shard)
        shard["modules"].append(mod)
        shard["bytes"] += size
        owner[mod] = i
    shards, owner = split_graph(files, deps, height, foundations)
    for i in sorted(range(len(shards)), key=lambda i: shards[i]["stage"]):
        shard = shards[i]
        assert all(shards[d]["stage"] < shard["stage"] for d in shard["deps"])
        shard["deps"] = sorted(shard["deps"])
        shard["key"] = digest([config] + [m + ":" + files[m][0] for m in shard["modules"]] +
                              sorted(shards[d]["key"] for d in shard["deps"]))
    return {"schema": 1, "config": config, "head": git("rev-parse", "HEAD").decode().strip(),
            "root": owner["Main"], "modules": len(height), "edges": sum(len(deps[m]) for m in height),
            "depth": height["Main"] + 1, "shards": shards}


if __name__ == "__main__":
    data = plan()
    with gzip.open(sys.argv[1], "wt") as out:
        json.dump(data, out, separators=(",", ":"))
    print({k: v for k, v in data.items() if k != "shards"})
    print("Shards per wave:", sorted(collections.Counter(s["stage"] for s in data["shards"]).items()))
    print("Total shards:", len(data["shards"]))

