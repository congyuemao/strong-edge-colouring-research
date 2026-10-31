"""exp34: exact search for depth-1-stuck states of the Kempe insertion lemma (NEW_DIRECTIONS 11).

Question for a fixed graph G and edge e: is there a strong 20-colouring of E(G) - e (conflicts in G) such that
  (blocked)   every colour occurs on N(e), and
  (stuck)     no colour pair (a, b) is separable at e?
Separability of (a, b) has a witness: a set C of edges, all coloured a or b, with no a- or b-coloured edge on its
L^2-boundary, containing every a-coloured member of N(e) and no b-coloured one.  (Take C = union of the (a, b)-
components that meet the a-members.)  Conversely any such C makes (a, b) separable.  So "stuck" is the conjunction,
over all sets C and ordered pairs (c, d), of the clause
    OR_{h in C} not y_cd(h)  OR  OR_{h in bd C} y_cd(h)  OR  OR_{f in N(e) - C} x_c(f)  OR  OR_{f in N(e) cap C} x_d(f),
with y_cd(h) <-> x_c(h) or x_d(h).  These clauses are added lazily: solve, read off the separable pairs of the
model, add the clauses of their witnesses for all ordered colour pairs, repeat.  UNSAT means no stuck state exists
on (G, e); a model that survives is a counterexample to one-pair insertion and is then tested at depth 2 and 3.
Colour symmetry is broken by fixing the colours of the six edges sharing an endpoint with e (a clique in L^2)
and by value precedence for the remaining colours (colour c+1 is used only after colour c, in a BFS order from e).

Environment: KIL_BUDGET = conflict budget per solver call (default 3000000); KIL_CKPT_DIR = directory for
checkpoints (the witness sets, saved after every iteration and reloaded on restart).

Usage: exp34_sat_kil.py g14 index edge | g14all index | random n girth seed [edge] | batch n girth seeds edges
       | tree
"""
import itertools
import json
import os
import sys
import time

import networkx as nx
from pysat.solvers import Solver

from exp33_kempe import K, l2_adj, separable, component, load, depth_two
from exp33b_adversary import deep_search

PAIRS = list(itertools.combinations(range(K), 2))
PIDX = {p: i for i, p in enumerate(PAIRS)}


class KilSat:
    def __init__(self, edges, e):
        self.edges, self.e = edges, e
        self.adj = adj = l2_adj(edges)
        self.m = m = len(edges)
        self.N = adj[e]
        self.x = lambda h, c: 1 + h * K + c
        ybase = 1 + m * K
        self.y = lambda c, d, h: ybase + PIDX[(min(c, d), max(c, d))] * m + h
        self.s = Solver(name="cadical195")
        self.nclauses = 0
        add = self.add
        others = [h for h in range(m) if h != e]
        for h in others:
            add([self.x(h, c) for c in range(K)])
            for c, d in PAIRS:
                add([-self.x(h, c), -self.x(h, d)])
            for c, d in PAIRS:
                add([-self.y(c, d, h), self.x(h, c), self.x(h, d)])
                add([self.y(c, d, h), -self.x(h, c)])
                add([self.y(c, d, h), -self.x(h, d)])
        for h in others:
            for g in adj[h]:
                if g > h and g != e:
                    for c in range(K):
                        add([-self.x(h, c), -self.x(g, c)])
        for c in range(K):                                  # blocked
            add([self.x(f, c) for f in self.N])
        a, b = edges[e]
        near = [f for f in self.N if a in edges[f] or b in edges[f]]
        for i, f in enumerate(near):                        # symmetry: the near clique gets colours 0, 1, ...
            add([self.x(f, i)])
        self.near = near
        # value precedence for the interchangeable colours len(near)..K-1, along N(e) first, then by L^2-distance
        order, seen_o = [], set(near) | {e}
        frontier = [f for f in self.N if f not in seen_o]
        while frontier:
            nxt = []
            for f in frontier:
                if f not in seen_o:
                    seen_o.add(f)
                    order.append(f)
                    nxt.extend(adj[f])
            frontier = nxt
        order += [h for h in range(m) if h not in seen_o]
        for c in range(len(near), K - 1):
            for i, h in enumerate(order):
                add([-self.x(h, c + 1)] + [self.x(g, c) for g in order[:i]])
        self.seen = set()
        for f in self.N:                                    # singleton witnesses C = {f} up front
            self.add_witness(frozenset([f]))

    def add(self, cl):
        self.s.add_clause(cl)
        self.nclauses += 1

    def add_witness(self, C):
        if C in self.seen:
            return False
        self.seen.add(C)
        bd = set()
        for h in C:
            bd.update(self.adj[h])
        bd -= C
        bd.discard(self.e)
        inN = [f for f in self.N if f in C]
        outN = [f for f in self.N if f not in C]
        for c in range(K):
            for d in range(K):
                if c == d:
                    continue
                cl = [-self.y(c, d, h) for h in C] + [self.y(c, d, h) for h in bd]
                cl += [self.x(f, c) for f in outN] + [self.x(f, d) for f in inN]
                self.add(cl)
        return True

    def load_checkpoint(self, path):
        if path and os.path.exists(path):
            with open(path) as fh:
                sets = json.load(fh)
            added = sum(self.add_witness(frozenset(C)) for C in sets)
            print(f"    resumed from {path}: {added} witness sets", flush=True)

    def save_checkpoint(self, path):
        if path:
            with open(path + ".tmp", "w") as fh:
                json.dump(sorted(sorted(C) for C in self.seen), fh)
            os.replace(path + ".tmp", path)

    def run(self, t0, max_iter=100000, budget=int(os.environ.get("KIL_BUDGET", 3_000_000)), ckpt=None):
        self.load_checkpoint(ckpt)
        it = 0
        while it < max_iter:
            it += 1
            ts = time.time()
            self.s.conf_budget(budget)
            r = self.s.solve_limited()
            if r is None:
                return f"OPEN (solver budget {budget} conflicts exhausted)", it, None
            if not r:
                return "UNSAT", it, None
            model = self.s.get_model()
            col = [-1] * self.m
            for h in range(self.m):
                if h == self.e:
                    continue
                cs = [c for c in range(K) if model[self.x(h, c) - 1] > 0]
                assert len(cs) == 1
                col[h] = cs[0]
            assert all(col[g] != col[h] for h in range(self.m) if h != self.e for g in self.adj[h] if g != self.e)
            assert len({col[f] for f in self.N}) == K
            new = 0
            nsep = 0
            for a, b in PAIRS:
                if separable(self.adj, col, self.e, a, b) is None:
                    continue
                nsep += 1
                for side in (a, b):
                    C = set()
                    for f in self.N:
                        if col[f] == side and f not in C:
                            C.update(component(self.adj, col, f, a, b))
                    new += self.add_witness(frozenset(C))
            if nsep == 0:
                return "STUCK", it, col
            self.save_checkpoint(ckpt)
            print(f"    iter {it}: model had {nsep} separable pairs; witness sets {len(self.seen)}, "
                  f"clauses {self.nclauses}; solve {time.time() - ts:.0f}s  [{time.time() - t0:.0f}s]", flush=True)
            if new == 0:
                raise RuntimeError("no new witness clause: encoding bug")
        return "OPEN", it, None


def report(name, edges, e, t0):
    report_result(KilSat(edges, e), name, e, t0)


def report_result(ks, name, e, t0):
    edges = ks.edges
    print(f"{name}, edge {e} {edges[e]}: m={len(edges)}, d(e)={len(ks.N)}, near={len(ks.near)}", flush=True)
    if len(ks.N) < K:
        print("    d(e) < 20: never blocked", flush=True)
        return
    tag = f"{name}_e{e}".replace(" ", "_").replace("=", "").replace("#", "")
    ckpt = os.path.join(os.environ["KIL_CKPT_DIR"], f"kil_{tag}.json") if os.environ.get("KIL_CKPT_DIR") else None
    res, it, col = ks.run(t0, ckpt=ckpt)
    msg = f"    -> {res} after {it} iterations, {len(ks.seen)} witness sets, {ks.nclauses} clauses"
    if res == "STUCK":
        d2 = depth_two(ks.adj, list(col), e)
        msg += "; depth 2: " + ("repaired" if d2 else
                               f"fails; BFS depth<=3: {deep_search(ks.adj, col, e, 3)}")
        msg += f"\n    colouring: {col}"
    print(msg + f"  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    t0 = time.time()
    mode = sys.argv[1]
    if mode == "g14":
        gi, e = int(sys.argv[2]), int(sys.argv[3])
        edges = next(ed for i, ed in enumerate(load(14)) if i == gi)
        report(f"n=14 #{gi}", edges, e, t0)
    elif mode == "random":
        from graphs_hg import random_girth
        n, g, seed = map(int, sys.argv[2:5])
        G = random_girth(n, g, seed) if g > 3 else nx.random_regular_graph(4, n, seed=seed)
        edges = [tuple(x) for x in G.edges()]
        e = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        report(f"random n={n} girth={nx.girth(G)} seed={seed}", edges, e, t0)
    elif mode == "batch":
        # batch n girth seeds edges: e.g. batch 24 5 0,1,2 0,7,19
        from graphs_hg import random_girth
        n, g = int(sys.argv[2]), int(sys.argv[3])
        for seed in map(int, sys.argv[4].split(",")):
            G = random_girth(n, g, seed) if g > 3 else nx.random_regular_graph(4, n, seed=seed)
            if G is None:
                print(f"n={n} girth>={g} seed={seed}: generation failed", flush=True)
                continue
            edges = [tuple(x) for x in G.edges()]
            for e in map(int, sys.argv[5].split(",")):
                report(f"random n={n} girth={nx.girth(G)} seed={seed}", edges, e, t0)
    elif mode == "g14all":
        # every edge with d(e) >= 20 of graph #index
        gi = int(sys.argv[2])
        edges = next(ed for i, ed in enumerate(load(14)) if i == gi)
        adj = l2_adj(edges)
        for e in range(len(edges)):
            if len(adj[e]) >= K:
                report(f"n=14 #{gi}", edges, e, t0)
    elif mode == "tree":
        # saturation on the tree: edges within distance 4 of an edge of the 4-regular tree, first solve only
        # (chains leaving the ball are not modelled, so only the singleton witnesses are meaningful here)
        T = nx.Graph()
        T.add_edge(0, 1)
        frontier, nxt = [0, 1], 2
        for depth in range(4):
            new = []
            for x in frontier:
                while T.degree(x) < 4:
                    T.add_edge(x, nxt)
                    new.append(nxt)
                    nxt += 1
            frontier = new
        edges = [tuple(x) for x in T.edges()]
        e = edges.index((0, 1))
        ks = KilSat(edges, e)
        print(f"tree ball: {len(edges)} edges, d(e) = {len(ks.N)}", flush=True)
        r = ks.s.solve()
        print("blocked + every singleton saturated:", "SAT" if r else "UNSAT", f"[{time.time() - t0:.0f}s]", flush=True)
