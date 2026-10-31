"""exp37: exp34's exact search for Kempe-stuck states, split into cubes that run in parallel (with runner.py) and
share their witness sets.

Cubes.  exp34 fixes the six near edges of e to colours 0..5 and orders the other edges (far conflicts of e first,
then by L^2-distance) with value precedence for colours 6..19.  A cube fixes the colours of the first t edges of
that order.  Enumerating every prefix assignment that is proper (among these edges and against the near edges) and
obeys precedence (a new colour >= 6 is always the next unused one) covers every model of the base formula, so:
all cubes UNSAT  <=>  no stuck state on (G, e);  any cube with a surviving model is a counterexample.

Witness sharing.  A witness clause forbids a separable configuration for all ordered colour pairs and does not
depend on the cube, so it is valid for every cube.  Each cube appends its new witness sets to pool/<cube>.jsonl and
before every solve absorbs the new lines of all pool files.  The pool is also the checkpoint: a restarted cube
reloads everything.  Each cube ends with a line "RESULT UNSAT", "RESULT STUCK <colouring>", "RESULT OPEN" or
"RESULT SPLIT".

Adaptive splitting.  The solver runs in slices of KIL_SLICE conflicts (default 200000); once a cube has used
KIL_SPLIT_AFTER seconds of CPU time (default 900; 0 = never), it stops and splits on the next edge of the order:
one sub-cube per colour that edge may take (proper against the cube, value precedence), written to
spawn/<cube>.jsonl for runner.py.  The sub-cubes cover the cube, so a split cube counts as covered.  CPU time, not
wall time, so a paused job does not split everything on resume.  Sub-cube ids extend the parent id: cube0012.7.3.

Usage: exp37_kil_cubes.py make <jobdir> n girth seed edge t      write the cube tasks (for runner.py)
       exp37_kil_cubes.py cube <jobdir> n girth seed edge t index [c1,c2,..]
                                                  solve one cube (extended by colours c1, c2, .. on the next edges)
       exp37_kil_cubes.py verdict <jobdir>                         combine the cube results
"""
import json
import os
import sys
import time

import networkx as nx

from exp33_kempe import K, separable, component, depth_two
from exp34_sat_kil import KilSat, PAIRS
from graphs_hg import random_girth

PY = os.path.abspath(sys.executable)
HERE = os.path.dirname(os.path.abspath(__file__))


def build(n, g, seed, e):
    G = random_girth(n, g, seed) if g > 3 else nx.random_regular_graph(4, n, seed=seed)
    return [tuple(x) for x in G.edges()], nx.girth(G)


def prefix_order(ks):
    """The edges in the order used by the value-precedence constraints (as in KilSat.__init__)."""
    adj, e = ks.adj, ks.e
    order, seen = [], set(ks.near) | {e}
    frontier = [f for f in ks.N if f not in seen]
    while frontier:
        nxt = []
        for f in frontier:
            if f not in seen:
                seen.add(f)
                order.append(f)
                nxt.extend(adj[f])
        frontier = nxt
    return order


def extensions(ks, order, assign, i):
    """Colours order[i] may take given the colours `assign` of order[:i]: proper against the near edges (colours
    0..5) and the assigned edges, and a new colour >= 6 only if it is the next unused one (value precedence)."""
    fixed = {f: c for c, f in enumerate(ks.near)}
    ff = len(ks.near)
    h = order[i]
    banned = {fixed[g] for g in ks.adj[h] if g in fixed} | {assign[g] for g in ks.adj[h] if g in assign}
    top = max([ff] + [assign[g] + 1 for g in order[:i] if assign[g] >= ff])
    return [c for c in list(range(ff)) + list(range(ff, min(top + 1, K))) if c not in banned]


def cubes(ks, t):
    order = prefix_order(ks)[:t]
    out = []

    def rec(i, assign):
        if i == len(order):
            out.append(dict(assign))
            return
        for c in extensions(ks, order, assign, i):
            assign[order[i]] = c
            rec(i + 1, assign)
            del assign[order[i]]

    rec(0, {})
    return order, out


def cube_id(index, extra):
    return f"cube{index:04d}" + "".join(f".{c}" for c in extra)


def task(job, n, g, seed, e, t, index, extra=()):
    cmd = [PY, "exp37_kil_cubes.py", "cube", job, str(n), str(g), str(seed), str(e), str(t), str(index)]
    if extra:
        cmd.append(",".join(map(str, extra)))
    return {"id": cube_id(index, extra), "cwd": HERE, "cmd": cmd, "env": {"PYTHONIOENCODING": "utf-8"}}


class Pool:
    def __init__(self, job, me):
        self.dir = os.path.join(job, "pool")
        os.makedirs(self.dir, exist_ok=True)
        self.mine = os.path.join(self.dir, f"{me}.jsonl")
        self.offsets = {}

    def absorb(self, ks):
        added = 0
        for name in os.listdir(self.dir):
            if not name.endswith(".jsonl"):
                continue
            path = os.path.join(self.dir, name)
            with open(path, encoding="utf-8") as fh:
                fh.seek(self.offsets.get(path, 0))
                while True:
                    line = fh.readline()
                    if not line or not line.endswith("\n"):
                        break                                   # a partial line is re-read next time
                    self.offsets[path] = fh.tell()
                    added += ks.add_witness(frozenset(json.loads(line)))
        return added

    def publish(self, sets):
        with open(self.mine, "a", encoding="utf-8") as fh:
            for C in sets:
                fh.write(json.dumps(sorted(C)) + "\n")


def solve_cube(job, n, g, seed, e, t, index, extra=()):
    t0 = time.time()
    me = cube_id(index, extra)
    spawn = os.path.join(job, "spawn", f"{me}.jsonl")
    if os.path.exists(spawn):                                   # split before a crash: nothing left to do
        print(f"RESULT SPLIT (already split into {sum(1 for _ in open(spawn))} sub-cubes)", flush=True)
        return
    edges, girth = build(n, g, seed, e)
    ks = KilSat(edges, e)
    full = prefix_order(ks)
    order, cs = cubes(ks, t)
    cube = dict(cs[index])
    for i, c in enumerate(extra):
        assert c in extensions(ks, full, cube, t + i), "invalid sub-cube"
        cube[full[t + i]] = c
    depth = t + len(extra)
    assume = [ks.x(h, c) for h, c in cube.items()]
    pool = Pool(job, me)
    budget = int(os.environ.get("KIL_BUDGET", 200_000_000))
    sl = int(os.environ.get("KIL_SLICE", 200_000))
    split_after = float(os.environ.get("KIL_SPLIT_AFTER", 900))
    c0 = time.process_time()
    print(f"n={n} girth={girth} seed={seed} edge {e}; cube {me} of {len(cs)} (depth {depth}): {cube}", flush=True)
    it = 0
    while True:
        it += 1
        got = pool.absorb(ks)
        ts = time.time()
        used, r = 0, None
        while True:
            ks.s.conf_budget(sl)
            r = ks.s.solve_limited(assumptions=assume)
            used += sl
            if r is not None:
                break
            if split_after and time.process_time() - c0 > split_after and depth < len(full):
                kids = extensions(ks, full, cube, depth)
                if not kids:
                    print(f"RESULT UNSAT (edge {full[depth]} has no colour left)  [{time.time() - t0:.0f}s]",
                          flush=True)
                    return
                os.makedirs(os.path.dirname(spawn), exist_ok=True)
                with open(spawn + ".tmp", "w", encoding="utf-8") as fh:
                    for c in kids:
                        fh.write(json.dumps(task(job, n, g, seed, e, t, index, list(extra) + [c])) + "\n")
                os.replace(spawn + ".tmp", spawn)
                print(f"RESULT SPLIT into {len(kids)} sub-cubes on edge {full[depth]} (colours {kids}) after {it} "
                      f"iterations, {time.process_time() - c0:.0f}s CPU  [{time.time() - t0:.0f}s]", flush=True)
                return
            if used >= budget:
                print(f"RESULT OPEN (budget {budget} conflicts) after {it} iterations  [{time.time() - t0:.0f}s]",
                      flush=True)
                return
        if not r:
            print(f"RESULT UNSAT after {it} iterations, {len(ks.seen)} witness sets  [{time.time() - t0:.0f}s]",
                  flush=True)
            return
        model = ks.s.get_model()
        col = [-1] * ks.m
        for h in range(ks.m):
            if h != e:
                col[h] = next(c for c in range(K) if model[ks.x(h, c) - 1] > 0)
        new, nsep = [], 0
        for a, b in PAIRS:
            if separable(ks.adj, col, e, a, b) is None:
                continue
            nsep += 1
            for side in (a, b):
                C = set()
                for f in ks.N:
                    if col[f] == side and f not in C:
                        C.update(component(ks.adj, col, f, a, b))
                C = frozenset(C)
                if ks.add_witness(C):
                    new.append(C)
        if nsep == 0:
            d2 = depth_two(ks.adj, list(col), e)
            print(f"RESULT STUCK depth2={'repaired' if d2 else 'fails'} colouring={col}  [{time.time() - t0:.0f}s]",
                  flush=True)
            return
        pool.publish(new)
        print(f"iter {it}: absorbed {got}, model had {nsep} separable pairs, +{len(new)} witness sets "
              f"(total {len(ks.seen)}); solve {time.time() - ts:.0f}s  [{time.time() - t0:.0f}s]", flush=True)


def make(job, n, g, seed, e, t):
    edges, girth = build(n, g, seed, e)
    ks = KilSat(edges, e)
    order, cs = cubes(ks, t)
    os.makedirs(job, exist_ok=True)
    with open(os.path.join(job, "tasks_src.jsonl"), "w", encoding="utf-8") as fh:
        for i in range(len(cs)):
            fh.write(json.dumps(task(job, n, g, seed, e, t, i)) + "\n")
    print(f"n={n} girth={girth} seed={seed} edge {e}: prefix {order}; {len(cs)} cubes written to {job}")


def verdict(job):
    res = {}
    with open(os.path.join(job, "results.jsonl"), encoding="utf-8") as fh:
        for line in fh:
            r = json.loads(line)
            res[r["id"]] = r
    from runner import load_tasks
    ids = [x["id"] for x in load_tasks(job)]                  # includes the sub-cubes in spawn/
    kinds = {}
    for i in ids:
        last = res.get(i, {}).get("last", "")
        k = last.split()[1] if last.startswith("RESULT") else ("RUNNING/PENDING" if i not in res else "ERROR")
        kinds.setdefault(k, []).append(i)
    print({k: len(v) for k, v in kinds.items()})
    if "STUCK" in kinds:
        print("COUNTEREXAMPLE in", kinds["STUCK"][:5])
    elif set(kinds) <= {"UNSAT", "SPLIT"}:
        print("ALL CUBES UNSAT (split cubes are covered by their sub-cubes): no stuck state on this (G, e)")


if __name__ == "__main__":
    m = sys.argv[1]
    if m == "make":
        make(sys.argv[2], *map(int, sys.argv[3:8]))
    elif m == "cube":
        extra = [int(c) for c in sys.argv[9].split(",")] if len(sys.argv) > 9 else []
        solve_cube(sys.argv[2], *map(int, sys.argv[3:9]), extra)
    elif m == "verdict":
        verdict(sys.argv[2])
