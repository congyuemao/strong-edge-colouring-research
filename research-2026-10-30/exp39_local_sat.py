"""exp39: exact local decisions around the GPU adversary's best states (exp38).

The GPU hunt finds colourings with only a few separable pairs left at e, but a heuristic can never show that no
stuck state exists.  Here the exact search of exp34 is run on a neighbourhood of such a state: free a set of edges
around e (see region()), fix every other edge to the state's colour, and ask whether some recolouring of the
free edges is blocked and depth-1 stuck (lazy witness clauses as in exp34; no colour symmetry breaking, since the
fixed edges pin the colour names).
    STUCK -> a genuine counterexample to one-pair insertion, then tested at depth 2 and by swap sequences up to 3;
    UNSAT -> no stuck state agrees with this colouring outside the free set.

Usage: exp39_local_sat.py make <jobdir> <hunt outdir> edges states_per_edge region[,region..]
           take the lowest `edges` edges of the hunt, up to `states_per_edge` distinct best states each, and write
           states.json and the runner tasks (one per state and region; regions as in region())
       exp39_local_sat.py one <jobdir> index region
       exp39_local_sat.py summary <jobdir>
KIL_TIME_LIMIT = seconds per task (default 1800; the task then reports OPEN).
"""
import json
import os
import sys
import threading
import time
from collections import deque

import numpy as np
from pysat.card import CardEnc, EncType

from exp33_kempe import l2_adj, depth_two
from exp33b_adversary import energy, deep_search
from exp34_sat_kil import KilSat
from exp38_gpu_adversary import build_instances, parse_specs, from_bits, proper

PY = os.path.abspath(sys.executable)
HERE = os.path.dirname(os.path.abspath(__file__))


def region(edges, adj, e, col, spec):
    """Free edges: "h<k>" (handled in one()) = all edges, at most k of them recoloured;
    "1", "2", .. = L^2-ball of that radius around e; "v2" = edges with an endpoint at graph distance
    <= 2 from e's endpoints; "t" = N(e) plus the L^2-neighbourhoods of the members of N(e) coloured by a separable
    pair (the edges whose colours must change to kill the remaining pairs)."""
    if spec == "t":
        from exp33_kempe import K, separable
        hot = set()
        for a in range(K):
            for b in range(a + 1, K):
                if separable(adj, col, e, a, b) is not None:
                    hot.update(f for f in adj[e] if col[f] in (a, b))
        free = set(adj[e])
        for f in hot:
            free.update(adj[f])
        free.discard(e)
        return free
    if spec.startswith("v"):
        k = int(spec[1:])
        nb = {}
        for x, y in edges:
            nb.setdefault(x, []).append(y)
            nb.setdefault(y, []).append(x)
        dist, q = {v: 0 for v in edges[e]}, deque(edges[e])
        while q:
            v = q.popleft()
            for w in nb[v]:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    q.append(w)
        return {h for h, (x, y) in enumerate(edges) if h != e and min(dist[x], dist[y]) <= k}
    return ball(adj, e, int(spec))


def ball(adj, e, r):
    dist = {e: 0}
    q = deque([e])
    while q:
        h = q.popleft()
        if dist[h] == r:
            continue
        for g in adj[h]:
            if g not in dist:
                dist[g] = dist[h] + 1
                q.append(g)
    return {h for h, d in dist.items() if d >= 1}


def make(job, hunt, n_edges, per_edge, radii):
    meta = json.load(open(os.path.join(hunt, "meta.json"), encoding="utf-8"))["meta"]
    d = np.load(os.path.join(hunt, "state.npz"))
    insts = build_instances(parse_specs(meta["spec"]))
    per = meta["per"]
    bE = d["bestEs"].reshape(len(insts), per)
    states = []
    for i in np.argsort(bE.min(axis=1), kind="stable")[:n_edges]:
        x, seen = insts[i], set()
        for j in np.argsort(bE[i], kind="stable"):
            col = from_bits(d["bcls"][i * per + j], len(x["adj"]))
            if tuple(col) in seen:
                continue
            seen.add(tuple(col))
            assert proper(x["adj"], col, x["e"]) and energy(x["adj"], col, x["e"]) == bE[i][j]
            states.append({"name": x["name"], "edges": x["edges"], "e": x["e"], "energy": int(bE[i][j]), "col": col})
            if len(seen) == per_edge:
                break
    os.makedirs(job, exist_ok=True)
    with open(os.path.join(job, "states.json"), "w", encoding="utf-8") as fh:
        json.dump(states, fh)
    with open(os.path.join(job, "tasks_src.jsonl"), "w", encoding="utf-8") as fh:
        for r in radii:
            for k in range(len(states)):
                fh.write(json.dumps({"id": f"r{r}_s{k:03d}", "cwd": HERE, "env": {"PYTHONIOENCODING": "utf-8"},
                                     "cmd": [PY, "exp39_local_sat.py", "one", job, str(k), str(r)]}) + "\n")
    print(f"{len(states)} states from {n_edges} edges (energies {sorted({s['energy'] for s in states})}); "
          f"{len(states) * len(radii)} tasks in {job}")


def one(job, k, r):  # r: region spec (see region())
    t0 = time.time()
    limit = float(os.environ.get("KIL_TIME_LIMIT", 1800))

    def watchdog():                             # the SAT call cannot be interrupted, so end the process instead
        time.sleep(limit)
        print(f"RESULT OPEN (time limit {limit:.0f}s)  [{time.time() - t0:.0f}s]", flush=True)
        os._exit(0)

    threading.Thread(target=watchdog, daemon=True).start()
    st = json.load(open(os.path.join(job, "states.json"), encoding="utf-8"))[k]
    edges, e, col = [tuple(x) for x in st["edges"]], st["e"], st["col"]
    adj = l2_adj(edges)
    if r.startswith("h"):                       # Hamming ball: every edge free, at most int(r[1:]) of them changed
        ks = KilSat(edges, e, fixed={})
        lits = [-ks.x(h, col[h]) for h in range(len(edges)) if h != e]
        for cl in CardEnc.atmost(lits, bound=int(r[1:]), top_id=len(edges) * (20 + 190),
                                 encoding=EncType.totalizer).clauses:
            ks.add(cl)
        print(f"{st['name']} state {k} (energy {st['energy']}): at most {r[1:]} of {len(lits)} edges recoloured",
              flush=True)
    else:
        free = region(edges, adj, e, col, r)
        fixed = {h: col[h] for h in range(len(edges)) if h != e and h not in free}
        print(f"{st['name']} state {k} (energy {st['energy']}): region {r}, {len(free)} free edges, "
              f"{len(fixed)} fixed", flush=True)
        ks = KilSat(edges, e, fixed=fixed)
    res, it, new = ks.run(t0)
    msg = f"RESULT {res.split()[0]} after {it} iterations, {len(ks.seen)} witness sets"
    if res == "STUCK":
        assert proper(adj, new, e) and energy(adj, new, e) == 0
        d2 = depth_two(adj, list(new), e)
        msg += "; depth 2: " + ("repaired" if d2 else f"fails; swap sequences up to 3: {deep_search(adj, new, e, 3)}")
        msg += f"; colouring {new}"
    print(msg + f"  [{time.time() - t0:.0f}s]", flush=True)


def summary(job):
    states = json.load(open(os.path.join(job, "states.json"), encoding="utf-8"))
    res = {}
    with open(os.path.join(job, "results.jsonl"), encoding="utf-8") as fh:
        for line in fh:
            r = json.loads(line)
            res[r["id"]] = r
    table = {}
    for tid, r in sorted(res.items()):
        rad, k = tid[1:].split("_s")
        kind = r["last"].split()[1] if r["last"].startswith("RESULT") else "ERROR"
        table.setdefault(rad, {}).setdefault(kind, []).append((int(k), round(r["end"] - r["start"])))
    for rad, kinds in sorted(table.items()):
        print(f"region {rad}: " + ", ".join(f"{k} {len(v)}" for k, v in sorted(kinds.items()))
              + f"; median time {int(np.median([t for v in kinds.values() for _, t in v]))}s")
        for k, v in kinds.items():
            if k != "UNSAT":
                print(f"  {k}: " + ", ".join(f"state {i} ({states[i]['name']}, energy {states[i]['energy']})"
                                             for i, _ in v[:10]))


if __name__ == "__main__":
    m = sys.argv[1]
    if m == "make":
        make(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6].split(","))
    elif m == "one":
        one(sys.argv[2], int(sys.argv[3]), sys.argv[4])
    elif m == "summary":
        summary(sys.argv[2])
