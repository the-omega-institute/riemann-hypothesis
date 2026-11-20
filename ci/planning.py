"""Coarsen the module DAG while keeping the available runner lanes supplied."""
from collections import defaultdict
import heapq


def split_graph(files, deps, height, foundations, lanes=500):
    shards = [{"modules": list(s["modules"]), "deps": set(), "stage": 0, "bytes": s["bytes"]}
              for s in foundations]
    owner = {m: i for i, s in enumerate(shards) for m in s["modules"]}
    users = defaultdict(list)
    for m in height:
        for d in set(deps[m]):
            users[d].append(m)
    tail = {}
    for m in sorted(height, key=height.get, reverse=True):
        tail[m] = 2048 + files[m][1] + max((tail[u] for u in users[m]), default=0)
    # Prioritise modules with the longest outstanding path to Main. Keep modules
    # sharing a single unfinished predecessor together when they fit in the packet.
    remaining = {m: sum(d not in owner for d in set(deps[m])) for m in height if m not in owner}
    ready = [(-tail[m], m) for m, n in remaining.items() if not n]
    heapq.heapify(ready)
    wave_start = len(shards)
    while ready:
        # Scale granularity to this frontier. A short tail can follow its own
        # dependencies in one process. A wide frontier is divided across lanes.
        target = min(180, max(20, (len(ready) + lanes - 1) // lanes))
        frontier = []
        while ready:
            local = []
            group = []
            size = 0
            while (local or ready) and len(group) < target and size < 1_000_000:
                _, m = heapq.heappop(local if local else ready)
                owner[m] = len(shards)
                group.append(m)
                size += files[m][1]
                for u in users[m]:
                    remaining[u] -= 1
                    if remaining[u] == 0:
                        # Same-packet chains avoid a full runner bootstrap per edge.
                        if all(owner[d] == len(shards) or owner[d] < wave_start for d in deps[u]):
                            heapq.heappush(local, (-tail[u], u))
                        else:
                            frontier.append((-tail[u], u))
            parents = {owner[d] for m in group for d in deps[m]} - {len(shards)}
            shards.append({"modules": group, "deps": parents, "bytes": size,
                           "stage": 1 + max((shards[i]["stage"] for i in parents), default=-1)})
            frontier.extend(local)
        ready = frontier
        heapq.heapify(ready)
        wave_start = len(shards)
    assert set(owner) == set(height)
    return shards, owner

