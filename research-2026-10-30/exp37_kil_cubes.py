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
reloads everything.  Each cube ends with a line "RESULT UNSAT", "RESULT STUCK <colouring>" or "RESULT OPEN".

Usage: exp37_kil_cubes.py make <jobdir> n girth seed edge t      write the cube tasks (for runner.py)
       exp37_kil_cubes.py cube <jobdir> n girth seed edge t index  solve one cube
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


def cubes(ks, t):
    order = prefix_order(ks)[:t]
    fixed = {f: i for i, f in enumerate(ks.near)}
    first_free = len(ks.near)
    out = []

    def rec(i, assign, top):
        if i == len(order):
            out.append(dict(assign))
            return
        h = order[i]
        banned = {fixed[g] for g in ks.adj[h] if g in fixed} | {assign[g] for g in ks.adj[h] if g in assign}
        for c in list(range(first_free)) + list(range(first_free, min(top + 1, K))):
            if c in banned:
                continue
            assign[h] = c
            rec(i + 1, assign, max(top, c + 1) if c >= first_free else top)
            del assign[h]

    rec(0, {}, first_free)
    return order, out


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


def solve_cube(job, n, g, seed, e, t, index):
    t0 = time.time()
    edges, girth = build(n, g, seed, e)
    ks = KilSat(edges, e)
    order, cs = cubes(ks, t)
    cube = cs[index]
    assume = [ks.x(h, c) for h, c in cube.items()]
    pool = Pool(job, f"cube{index:04d}")
    budget = int(os.environ.get("KIL_BUDGET", 200_000_000))
    print(f"n={n} girth={girth} seed={seed} edge {e}; cube {index}/{len(cs)}: {cube}", flush=True)
    it = 0
    while True:
        it += 1
        got = pool.absorb(ks)
        ts = time.time()
        ks.s.conf_budget(budget)
        r = ks.s.solve_limited(assumptions=assume)
        if r is None:
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
            fh.write(json.dumps({"id": f"cube{i:04d}", "cwd": HERE,
                                 "cmd": [PY, "exp37_kil_cubes.py", "cube", job, str(n), str(g), str(seed), str(e),
                                         str(t), str(i)]}) + "\n")
    print(f"n={n} girth={girth} seed={seed} edge {e}: prefix {order}; {len(cs)} cubes written to {job}")


def verdict(job):
    res = {}
    with open(os.path.join(job, "results.jsonl"), encoding="utf-8") as fh:
        for line in fh:
            r = json.loads(line)
            res[r["id"]] = r
    with open(os.path.join(job, "tasks.jsonl"), encoding="utf-8") as fh:
        ids = [json.loads(l)["id"] for l in fh if l.strip()]
    kinds = {}
    for i in ids:
        last = res.get(i, {}).get("last", "")
        k = last.split()[1] if last.startswith("RESULT") else ("RUNNING/PENDING" if i not in res else "ERROR")
        kinds.setdefault(k, []).append(i)
    print({k: len(v) for k, v in kinds.items()})
    if "STUCK" in kinds:
        print("COUNTEREXAMPLE in", kinds["STUCK"][:5])
    elif set(kinds) == {"UNSAT"}:
        print("ALL CUBES UNSAT: no stuck state on this (G, e)")


if __name__ == "__main__":
    m = sys.argv[1]
    if m == "make":
        make(sys.argv[2], *map(int, sys.argv[3:8]))
    elif m == "cube":
        solve_cube(sys.argv[2], *map(int, sys.argv[3:9]))
    elif m == "verdict":
        verdict(sys.argv[2])
