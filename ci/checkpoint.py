"""Copy completed siblings to durable Release storage before ending this wave."""
import json
import os
from pathlib import Path
import tempfile

from parts import INDEX, PLAN, asset_name, gzip, inventory, output, run, upload

repo = os.environ["GITHUB_REPOSITORY"]
run_id = os.environ["GITHUB_RUN_ID"]
shards = json.loads(gzip.decompress(PLAN.read_bytes()))["shards"]
available = json.loads(output("gh", "api", "--paginate", "--slurp",
                              f"repos/{repo}/actions/runs/{run_id}/artifacts?per_page=100"))
artifacts = {a["name"] for page in available for a in page["artifacts"] if not a["expired"]}
released = inventory(repo)
missing = []
for i in json.loads(os.environ["READY"]):
    key = shards[i]["key"]
    if asset_name(key) in released:
        continue
    if f"part-{i}" not in artifacts:
        missing.append(i)
        continue
    with tempfile.TemporaryDirectory() as tmp:
        run("gh", "run", "download", run_id, "-R", repo, "-n", f"part-{i}", "-D", tmp)
        upload(repo, key, Path(tmp) / asset_name(key))
if missing:
    raise SystemExit(f"Unfinished shards: {missing}. Completed siblings are available for reuse.")
