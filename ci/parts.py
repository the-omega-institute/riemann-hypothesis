"""Store Lake outputs in GitHub Releases and restore them by dependency digest."""
from contextlib import contextmanager
import gzip
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import tempfile
import zipfile
from concurrent.futures import FIRST_EXCEPTION, ThreadPoolExecutor, wait

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


def transient_error(message):
    return any(marker in message.lower() for marker in (
        "http 429", "http 500", "http 502", "http 503", "http 504", "connection reset",
        "connection refused", "connection timed out", "tls handshake timeout", "unexpected eof",
        "secondary rate limit",
    ))


def github_read(*args):
    for delay in (2, 5, 15, 30, 0):
        result = subprocess.run(["gh", *args], capture_output=True, text=True)
        if not result.returncode:
            return result.stdout.strip()
        message = result.stderr.strip()
        if not delay or not transient_error(message):
            raise RuntimeError(message)
        print(f"GitHub read failed ({message}), retrying in {delay}s", flush=True)
        time.sleep(delay)


def api_pages(endpoint):
    return json.loads(github_read("api", "--paginate", "--slurp", endpoint))


def select_group_archives(assets):
    """Prefer the assembled outputs consumed by downstream builds of this exact archive."""
    selected = assets.copy()
    for name, asset in assets.items():
        key = name.removesuffix(".tar.zst")
        group_name = key + ".groups-" + asset["digest"].removeprefix("sha256:") + ".tar.zst"
        if group_name in assets:
            selected[name] = assets[group_name]
    return selected


def inventory(repo, pages_for=api_pages):
    # Repositories start with zero buckets. Propagate API errors to avoid a false cache miss.
    pages = pages_for(f"repos/{repo}/releases?per_page=100")
    releases = [r for page in pages for r in page if r["tag_name"].startswith("lean-parts-v1-")]
    def assets(release):
        entries = release["assets"]
        # Fall back to the paginated endpoint at common nested-collection limits.
        if len(entries) in {30, 100, 1000}:
            url = f'repos/{repo}/releases/{release["id"]}/assets?per_page=100'
            pages = pages_for(url)
            entries = [a for page in pages for a in page]
        return {a["name"]: {"url": a["browser_download_url"], "digest": a["digest"], "size": a["size"]}
                for a in entries if a["state"] == "uploaded" and a.get("digest")
                and a["name"].endswith(".tar.zst") and bucket(a["name"]) == release["tag_name"]}
    return select_group_archives({name: a for release in releases for name, a in assets(release).items()})


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
    return data


def relative_module(path):
    for prefix in ("lib/lean/", "ir/"):
        if path.startswith(prefix):
            stem = path[len(prefix):].split(".", 1)[0]
            return stem.replace("/", ".")
    return None


def dependencies(modules, edges):
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


def download_ci_copy(number, name, asset, archive):
    repo = os.environ["GITHUB_REPOSITORY"]
    endpoint = f"repos/{repo}/actions/artifacts"
    pages = api_pages(f"{endpoint}?name=part-{number}&per_page=100")
    for page in pages:
        for artifact in page["artifacts"]:
            if artifact["expired"] or artifact["workflow_run"]["head_branch"] != "main":
                continue
            bundle = archive.with_suffix(".zip")
            with bundle.open("wb") as dest:
                result = subprocess.run(["gh", "api", f'{endpoint}/{artifact["id"]}/zip'], stdout=dest)
            if result.returncode:
                continue
            with zipfile.ZipFile(bundle) as cached:
                if name not in cached.namelist() or cached.getinfo(name).file_size != asset["size"]:
                    continue
                with cached.open(name) as src, archive.open("wb") as dest:
                    shutil.copyfileobj(src, dest)
                if "sha256:" + sha256(archive) == asset["digest"]:
                    print(f"Recovered {name} from Actions artifact {artifact['id']}", flush=True)
                    return
    raise RuntimeError(f"No retained Actions copy of {name}")


def fetch_archive(number, name, asset, archive):
    try:
        run("curl", "--fail", "--location", "--silent", "--show-error", "--retry", "4",
            "--retry-all-errors", "--retry-max-time", "300", "--output", str(archive), asset["url"])
    except subprocess.CalledProcessError:
        if not (os.environ.get("GITHUB_ACTIONS") == "true" and os.environ.get("GH_TOKEN")):
            raise
        download_ci_copy(number, name, asset, archive)
    if "sha256:" + sha256(archive) != asset["digest"]:
        raise ValueError("Release SHA-256 mismatch: " + asset["url"])


@contextmanager
def release_archive(number, name, asset):
    cache = os.environ.get("RH_RELEASE_CACHE_DIR")
    if not cache and os.environ.get("RUNNER_ENVIRONMENT") == "self-hosted":
        cache = Path(os.environ["RUNNER_TEMP"]).parent / "rh-release-cache"
    if not cache:
        with tempfile.TemporaryDirectory(dir=STATE) as tmp:
            archive = Path(tmp) / "part.zst"
            fetch_archive(number, name, asset, archive)
            yield archive
        return

    import fcntl
    import re
    digest = asset["digest"]
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", digest):
        raise ValueError(f"Invalid Release digest for {name}")
    key = digest.removeprefix("sha256:")
    directory = Path(cache) / key[:2]
    directory.mkdir(parents=True, exist_ok=True)
    archive = directory / (key + ".tar.zst")
    with (directory / (key + ".lock")).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not (archive.is_file() and archive.stat().st_size == asset["size"] and sha256(archive) == key):
            # Keep a partial download out of the cache until its Release digest matches.
            partial = directory / (key + ".partial")
            try:
                fetch_archive(number, name, asset, partial)
                partial.replace(archive)
            finally:
                partial.unlink(missing_ok=True)
                partial.with_suffix(".zip").unlink(missing_ok=True)
    yield archive


def unpack(number, name, asset, required):
    BUILD.mkdir(parents=True, exist_ok=True)
    with release_archive(number, name, asset) as archive:
        with subprocess.Popen(["zstd", "-qdc", archive], stdout=subprocess.PIPE) as reader:
            with tarfile.open(fileobj=reader.stdout, mode="r|") as tar:
                for entry in tar:
                    if relative_module(entry.name) in required:
                        if not entry.isfile():
                            raise ValueError(entry.name)
                        # Python 3.12 tarfile creates missing parents without exist_ok.
                        # Validate first, then create shared parents safely across workers.
                        member = tarfile.data_filter(entry, str(BUILD))
                        (BUILD / member.name).parent.mkdir(parents=True, exist_ok=True)
                        tar.extract(member, BUILD, filter="data")
            while reader.stdout.read(65536):
                pass
            reader.stdout.close()
            if reader.wait():
                raise RuntimeError("truncated zstd stream")


def restore(data, index, modules, edges=None, *, allow_missing=False):
    if edges is None:
        _, edges = graph()
    wanted = dependencies(modules, edges)
    if len(wanted) >= 80_000 and os.environ.get("RUNNER_ENVIRONMENT") == "github-hosted":
        run("bash", str(Path(__file__).with_name("large-workspace.sh")))
    def restore_one(item):
        number, shard = item
        needed = wanted.intersection(shard["modules"])
        key = shard["key"]
        name = asset_name(key)
        asset = index.get(name)
        marker = receipt(key)
        if asset and ".groups-" in asset["url"].rsplit("/", 1)[-1]:
            name = asset["url"].rsplit("/", 1)[-1]
            group_marker = receipt(name.removesuffix(".tar.zst"))
            # An older checkout may have installed the independent build in this workspace.
            if marker.exists():
                group_marker.unlink(missing_ok=True)
                marker.unlink()
            marker = group_marker
        installed = set(marker.read_text().splitlines()) if marker.exists() else set()
        needed = {m for m in needed if m not in installed or
                  not (BUILD / "lib/lean" / (m.replace(".", "/") + ".olean")).exists()}
        if needed:
            if allow_missing and asset is None:
                return
            if asset is None:
                raise KeyError(name)
            unpack(number, name, asset, needed)
            marker.parent.mkdir(parents=True, exist_ok=True)
            marker.write_text("\n".join(sorted(installed | needed)))

    shards = [(i, s) for i, s in enumerate(data["shards"]) if not wanted.isdisjoint(s["modules"])]
    ci = os.environ.get("GITHUB_ACTIONS") == "true"
    with ThreadPoolExecutor(max_workers=4) as pool:
        if not ci:
            list(pool.map(restore_one, shards))
            return
        print(f"Restoring {len(wanted)} required modules across {len(shards)} shards", flush=True)
        pending = {pool.submit(restore_one, shard) for shard in shards}
        while pending:
            done, pending = wait(pending, timeout=60, return_when=FIRST_EXCEPTION)
            for task in done:
                task.result()
            print(f"Restore checked {len(shards) - len(pending)}/{len(shards)} shards", flush=True)


def run_lake_ci(args, label):
    print(label, flush=True)
    started = time.monotonic()
    with subprocess.Popen(args) as process:
        while True:
            try:
                code = process.wait(timeout=60)
                break
            except subprocess.TimeoutExpired:
                elapsed = int(time.monotonic() - started)
                print(f"{label} — {elapsed}s elapsed", flush=True)
                # Sample only Lake and its immediate workers. CPU time is cumulative.
                try:
                    sample = subprocess.run([
                        "ps", "-p", str(process.pid), "--ppid", str(process.pid),
                        "--sort=-rss", "-o", "pid,stat,time,rss,comm",
                    ], capture_output=True, text=True, timeout=5)
                except (OSError, subprocess.TimeoutExpired):
                    continue
                if sample.returncode == 0:
                    print("\n".join(sample.stdout.splitlines()[:7]), flush=True)
        if code:
            raise subprocess.CalledProcessError(code, args)


def lake(modules, reuse=False):
    if not modules:
        return
    args = ["lake"]
    ci = os.environ.get("GITHUB_ACTIONS") == "true"
    if ci:
        # Plain progress reports newly built targets. Cached linter warnings stay muted.
        args.extend(["--no-ansi", "--log-level=error"])
    if reuse:
        args.append("--no-build")
    args.append("build")
    args.extend("+" + m + ":olean" for m in sorted(modules))
    if ci:
        action = "Checking released outputs for" if reuse else "Building"
        run_lake_ci(args, f"{action} {len(modules)} Lean module(s)")
    else:
        run(*args)


def build(data, index, number):
    shard = data["shards"][number]
    mods = set(shard["modules"])
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"Reading the import graph for shard {number}", flush=True)
    _, edges = graph()
    imports = {d for m in mods for d in edges[m]} - mods
    restore(data, index, imports, edges)
    lake(imports, reuse=True)
    lake(mods)
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"Packaging {len(mods)} modules for shard {number} and checking the archive with Lake", flush=True)
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


def audit(report_path=Path("axioms.txt")):
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
    report_path.write_text(result + "\n")


def upload(repo, key, path):
    tag = bucket(key)
    # Create only a bucket that actually has a completed part. Concurrent creators converge.
    endpoint = f"repos/{repo}/releases/tags/{tag}"
    try:
        release_id = github_read("api", endpoint, "--jq", ".id")
    except RuntimeError as exc:
        if "HTTP 404" not in str(exc):
            raise
        source = os.environ.get("BUILD_SOURCE_SHA") or output("git", "rev-parse", "HEAD")
        subprocess.run(["gh", "release", "create", tag, "-R", repo, "--target", source,
                        "--prerelease", "--latest=false", "--title", tag,
                        "--notes", "Reusable compiled Lake shards for Linux x86-64."])
        release_id = github_read("api", endpoint, "--jq", ".id")
    assets = f"repos/{repo}/releases/{release_id}/assets"
    url = f"https://uploads.github.com/{assets}?name={path.name}"
    expected = "sha256:" + sha256(path)
    for delay in (2, 5, 15, 30, 0):
        post = subprocess.run(["gh", "api", "--method", "POST", "-H", "Content-Type: application/octet-stream",
                               "--input", str(path), url, "--jq", ".digest"], capture_output=True, text=True)
        if not post.returncode:
            if post.stdout.strip() != expected:
                raise RuntimeError(f"Uploaded digest mismatch for {path.name}")
            return
        if not transient_error(post.stderr) and "HTTP 422" not in post.stderr:
            raise RuntimeError(post.stderr)
        # The server may have accepted the bytes before the connection failed.
        remote = next((a for page in api_pages(assets + "?per_page=100") for a in page
                       if a["name"] == path.name), None)
        if remote and remote["state"] == "uploaded":
            if remote["digest"] != expected:
                raise RuntimeError(f"Existing Release digest mismatch for {path.name}")
            return
        if remote and remote["state"] == "starter" and remote["size"] == 0:
            run("gh", "api", "--method", "DELETE", f'repos/{repo}/releases/assets/{remote["id"]}')
        if not delay:
            raise RuntimeError(post.stderr)
        print(f"Upload interrupted, retrying {path.name} in {delay}s", flush=True)
        time.sleep(delay)



def main():
    command, *args = sys.argv[1:]
    repo = os.environ.get("GITHUB_REPOSITORY", "the-omega-institute/riemann-hypothesis")
    if command == "publish":
        key, source = args
        os.environ["BUILD_SOURCE_SHA"] = source
        upload(repo, key, Path(asset_name(key)))
        return
    if command in {"prepare", "restore", "select"}:
        prepare(repo)
    if command == "prepare":
        return
    data = json.loads(gzip.decompress(PLAN.read_bytes()))
    index = json.loads(INDEX.read_text())
    if command == "select":
        from groups import assembly_inputs, complete_assemblies
        shards = data["shards"]
        numbers = json.loads(os.environ["PART_IDS"])
        present = {i for i, shard in enumerate(shards) if asset_name(shard["key"]) in index}
        pending = [n for n in numbers if n not in present]
        blocked = {n for n in pending if not present.issuperset(shards[n]["deps"])}
        missing = blocked - complete_assemblies(assembly_inputs(shards, blocked), index)
        if missing:
            raise ValueError(f"release prerequisites missing for shards {sorted(missing)}")
        selected = [{"number": n, "key": shards[n]["key"]} for n in pending]
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            print("matrix=" + json.dumps(selected), file=f)
    elif command == "build":
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

