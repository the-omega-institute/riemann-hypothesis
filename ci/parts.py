"""Store Lake outputs in GitHub Releases and restore them by dependency digest."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
from concurrent.futures import ThreadPoolExecutor

from plan import graph, plan

BUILD = Path(".lake/build")
STATE = Path(".lake/parts")
PLAN = STATE / "plan.json.gz"
INDEX = STATE / "release-assets.json"


def run(*args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def output(*args):
    return subprocess.check_output(args, text=True).strip()


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def bucket(key):
    return "lean-parts-v1-" + key[0]


def asset_name(key):
    return key + ".tar.zst"


def inventory(repo):
    # Repositories start with zero buckets. Propagate API errors to avoid a false cache miss.
    pages = json.loads(output("gh", "api", "--paginate", "--slurp",
                              f"repos/{repo}/releases?per_page=100"))
    releases = [r for page in pages for r in page if r["tag_name"].startswith("lean-parts-v1-")]
    def assets(release):
        url = f'repos/{repo}/releases/{release["id"]}/assets?per_page=100'
        pages = json.loads(output("gh", "api", "--paginate", "--slurp", url))
        return {a["name"]: {"url": a["browser_download_url"], "digest": a["digest"], "size": a["size"]}
                for page in pages for a in page if a["state"] == "uploaded" and a.get("digest")
                and a["name"].endswith(".tar.zst") and bucket(a["name"]) == release["tag_name"]}
    with ThreadPoolExecutor(max_workers=4) as pool:
        return {name: a for group in pool.map(assets, releases) for name, a in group.items()}


def prepare(repo):
    STATE.mkdir(parents=True, exist_ok=True)
    data = plan()
    with gzip.open(PLAN, "wt", encoding="utf-8") as f:
        json.dump(data, f, separators=(",", ":"))
    index = inventory(repo)
    INDEX.write_text(json.dumps(index))
    shards = data["shards"]
    present = {i for i, s in enumerate(shards) if asset_name(s["key"]) in index}
    ready = [i for i, s in enumerate(shards) if i not in present and present.issuperset(s["deps"])]
    if 0 not in present and 0 in ready:
        ready = [0]
    print(f'{data["modules"]} modules, {data["edges"]} imports, {len(shards)} shards; '
          f'{len(present)} released, {len(ready)} ready')
    if "GITHUB_OUTPUT" in os.environ:
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            print("ready=" + json.dumps(ready[:32]), file=f)
            print("complete=" + str(len(present) == len(shards)).lower(), file=f)
    return data


def relative_module(path):
    for prefix in ("lib/lean/", "ir/"):
        if path.startswith(prefix):
            stem = path[len(prefix):].split(".", 1)[0]
            return stem.replace("/", ".")
    return None


def dependencies(modules):
    _, edges = graph()
    seen = set()
    todo = list(modules)
    while todo:
        mod = todo.pop()
        if mod not in seen:
            seen.add(mod)
            todo.extend(edges[mod])
    return seen


def receipt(key):
    return STATE / "installed" / key


def unpack(asset, required):
    BUILD.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=STATE) as tmp:
        archive = Path(tmp) / "part.zst"
        run("curl", "--fail", "--location", "--silent", "--show-error", "--retry", "4",
            "--output", str(archive), asset["url"])
        if "sha256:" + sha256(archive) != asset["digest"]:
            raise ValueError("Release SHA-256 mismatch: " + asset["url"])
        with subprocess.Popen(["zstd", "-qdc", archive], stdout=subprocess.PIPE) as reader:
            with tarfile.open(fileobj=reader.stdout, mode="r|") as tar:
                for entry in tar:
                    if relative_module(entry.name) in required:
                        if not entry.isfile():
                            raise ValueError(entry.name)
                        tar.extract(entry, BUILD, filter="data")
            while reader.stdout.read(65536):
                pass
            reader.stdout.close()
            if reader.wait():
                raise RuntimeError("truncated zstd stream")


def restore(data, index, modules):
    wanted = dependencies(modules)
    for shard in data["shards"]:
        needed = wanted.intersection(shard["modules"])
        if not needed:
            continue
        key = shard["key"]
        marker = receipt(key)
        installed = set(marker.read_text().splitlines()) if marker.exists() else set()
        needed = {m for m in needed if m not in installed or
                  not (BUILD / "lib/lean" / (m.replace(".", "/") + ".olean")).exists()}
        if needed:
            unpack(index[asset_name(key)], needed)
            marker.parent.mkdir(parents=True, exist_ok=True)
            marker.write_text("\n".join(sorted(installed | needed)))


def lake(modules, reuse=False):
    if modules:
        run("lake", *(["--no-build"] if reuse else []), "build",
            *["+" + m + ":olean" for m in sorted(modules)])


def build(data, index, number):
    shard = data["shards"][number]
    mods = set(shard["modules"])
    _, edges = graph()
    imports = {d for m in mods for d in edges[m]} - mods
    restore(data, index, imports)
    lake(imports, reuse=True)
    lake(mods)
    archive = Path(asset_name(shard["key"])).resolve()
    paths = []
    for mod in sorted(mods):
        stem = mod.replace(".", "/")
        for prefix in ("lib/lean/", "ir/"):
            base = BUILD / (prefix + stem)
            paths += [p.relative_to(BUILD) for p in base.parent.glob(base.name + ".*")
                      if p.is_file() and not p.name.endswith(".setup.json")]
        if not (BUILD / ("lib/lean/" + stem + ".olean")).is_file():
            raise ValueError("missing compiled module " + mod)
    names = b"".join(os.fsencode(p) + b"\0" for p in sorted(paths))
    run("tar", "--zstd", "-cf", str(archive), "-C", str(BUILD), "--null", "-T", "-", input=names)
    # Remove this shard's outputs before the no-build test. Every restored file comes from its archive.
    for p in paths:
        (BUILD / p).unlink()
    run("tar", "--zstd", "-xf", str(archive), "-C", str(BUILD))
    lake(mods, reuse=True)
    return archive


def audit():
    result = output("lake", "env", "lean", "ci/Audit.lean")
    import re
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result)
    expected = {"riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
                "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"}
    if {name for name, _ in reports} != expected or any(
            set(x.strip() for x in axioms.split(",")) - {"propext", "Quot.sound", "Classical.choice"}
            for _, axioms in reports):
        raise ValueError("unexpected axiom report:\n" + result)
    print(result)
    Path("axioms.txt").write_text(result + "\n")


def upload(repo, key, path):
    tag = bucket(key)
    # Create only a bucket that actually has a completed part. Concurrent creators converge.
    if subprocess.run(["gh", "release", "view", tag, "-R", repo], stdout=subprocess.DEVNULL,
                      stderr=subprocess.DEVNULL).returncode:
        result = subprocess.run(["gh", "release", "create", tag, "-R", repo, "--target",
                                 output("git", "rev-parse", "HEAD"), "--prerelease", "--latest=false",
                                 "--title", tag, "--notes", "Reusable compiled Lake shards for Linux x86-64."])
        if result.returncode:
            run("gh", "release", "view", tag, "-R", repo)
    run("gh", "release", "upload", tag, "-R", repo, str(path))
    assets = json.loads(output("gh", "release", "view", tag, "-R", repo, "--json", "assets"))["assets"]
    remote = next(a for a in assets if a["name"] == path.name)
    if remote["digest"] != "sha256:" + sha256(path):
        raise RuntimeError("uploaded asset digest mismatch")


def main():
    command, *args = sys.argv[1:]
    repo = os.environ.get("GITHUB_REPOSITORY", "the-omega-institute/riemann-hypothesis")
    if command in {"prepare", "restore"}:
        prepare(repo)
    if command == "prepare":
        return
    data = json.loads(gzip.decompress(PLAN.read_bytes()))
    index = json.loads(INDEX.read_text())
    if command == "build":
        build(data, index, int(args[0]))
    elif command == "upload":
        key = data["shards"][int(args[0])]["key"]
        upload(repo, key, Path(asset_name(key)))
    elif command == "restore":
        mods = set(args or ["Main"])
        restore(data, index, mods)
        lake(mods, reuse=True)
    elif command == "finalize":
        restore(data, index, {"Main"})
        lake({"Main"}, reuse=True)
        audit()
        manifest = {s["key"]: index[asset_name(s["key"])] for s in data["shards"]}
        Path("release.json").write_text(json.dumps({"source": data["head"], "linux": "x86_64",
            "target": "Main", "parts": manifest}, indent=2) + "\n")
    else:
        raise ValueError(command)


if __name__ == "__main__":
    main()

