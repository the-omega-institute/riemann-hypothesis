"""Dispatch ready imports while other shard batches are running."""
import collections
import json
import os
import re
import time

from parts import INDEX, asset_name, inventory, output, prepare, run

BATCH = 28  # Run title fits GitHub's display limit, including all shard numbers.


def batches(repo, head):
    pages = json.loads(output("gh", "api", "--paginate", "--slurp",
                              f"repos/{repo}/actions/workflows/shard-batch.yml/runs?branch=main&per_page=100"))
    rows = []
    for page in pages:
        for r in page["workflow_runs"]:
            title = re.fullmatch(r"Parts ([0-9a-f]{40}) (\d+) (\[[0-9,]+\])", r["display_title"])
            if title and title[1] == head:
                rows.append((title[2], json.loads(title[3]), r["status"]))
    return rows


def schedule():
    repo = os.environ["GITHUB_REPOSITORY"]
    session = os.environ.get("BUILD_SESSION") or os.environ["GITHUB_RUN_ID"]
    data = prepare(repo)
    head, shards = data["head"], data["shards"]
    tail = [max(1, s["bytes"]) for s in shards]
    for i in sorted(range(len(shards)), key=lambda i: shards[i]["stage"], reverse=True):
        for p in shards[i]["deps"]:
            tail[p] = max(tail[p], shards[p]["bytes"] + tail[i])
    submitted = {}
    started = time.monotonic()
    while True:
        index = inventory(repo)
        present = {i for i, s in enumerate(shards) if asset_name(s["key"]) in index}
        INDEX.write_text(json.dumps(index))
        if len(present) == len(shards):
            with open(os.environ["GITHUB_OUTPUT"], "a") as f:
                print("complete=true", file=f)
            return
        rows = batches(repo, head)
        active = {i for _, ids, status in rows if status != "completed" for i in ids}
        attempts = collections.Counter(i for train, ids, _ in rows if train == session for i in ids)
        # Allow for the Actions API's eventual visibility after workflow_dispatch.
        now = time.monotonic()
        active.update(i for i, t in submitted.items() if now - t < 180)
        ready = [i for i, s in enumerate(shards) if i not in present and i not in active
                 and attempts[i] < 3 and present.issuperset(s["deps"])]
        ready.sort(key=lambda i: (-tail[i], i))
        print(f"{len(present)}/{len(shards)} released; {len(active - present)} outstanding; dispatching {len(ready)}", flush=True)
        if not ready and not active - present:
            raise RuntimeError("No buildable shards remain. Inspect failed batch jobs before resuming.")
        if now - started > 4 * 3600:
            run("gh", "workflow", "run", "lean-parts.yml", "-R", repo, "--ref", "main", "-f", f"session={session}")
            return
        for start in range(0, len(ready), BATCH):
            group = ready[start:start + BATCH]
            ids = json.dumps(group, separators=(",", ":"))
            run("gh", "workflow", "run", "shard-batch.yml", "-R", repo, "--ref", "main",
                "-f", f"source={head}", "-f", f"session={session}", "-f", f"parts={ids}")
            submitted.update(dict.fromkeys(group, time.monotonic()))
        time.sleep(60)


if __name__ == "__main__":
    schedule()

