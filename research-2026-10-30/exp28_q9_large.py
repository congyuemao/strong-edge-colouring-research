"""exp28: Q9 / "9 classes + 2 defect colours" on large graphs of medium girth (n up to thousands).

exp7 checked local descent with 9 classes only on graphs with <= 160 edges.  Here, on random 4-regular graphs
of girth g, the state is a partition of E into 9 classes with every class-degree in L^2 at most 2 (every class
is a union of paths and cycles of L^2).  The objective is the number of odd class cycles ("tokens").

  1. Lovasz descent on Phi_1 gives class-degrees <= 2.
  2. Token search.  Moving e from class p to class q is allowed if cnt[e][q] <= 2 and the q-neighbours of e
     have q-degree <= 1.  The change in #odd cycles is local: -1 if e's class-p component is an odd cycle,
     +1 if e's two q-neighbours are the ends of one class-q path with an even number of vertices (then the
     path plus e is a new odd cycle).  Moves with change <= 0 are accepted: 0 moves a token, -1 kills it.
     With probability p_env an arbitrary edge is moved instead (change <= 0), which reshapes the paths.
  3. Tokens that survive the step budget are described (lengths), and a defect set is sought by SAT: one
     edge per odd cycle, defect conflict graph 2-colourable (the 2 spare colours of the 9+2 scheme).

Usage: exp28_q9_large.py n g seed steps [p_env] [K]   (K = number of classes, default 9)
"""
import random
import sys
import time
from collections import Counter

import networkx as nx

from exp4_local_search import conflict_adj
from exp5b_high_girth import raise_girth

K = 9


class State:
    def __init__(self, adj, rng):
        self.adj, self.rng, self.m = adj, rng, len(adj)
        self.part = [rng.randrange(K) for _ in range(self.m)]
        self.cnt = [[0] * K for _ in range(self.m)]
        for i in range(self.m):
            for w in adj[i]:
                self.cnt[i][self.part[w]] += 1

    def own(self, i):
        return self.cnt[i][self.part[i]]

    def move(self, i, q):
        p = self.part[i]
        for w in self.adj[i]:
            self.cnt[w][p] -= 1
            self.cnt[w][q] += 1
        self.part[i] = q

    def descend(self):
        ch = True
        while ch:
            ch = False
            for i in range(self.m):
                q = min(range(K), key=lambda c: (self.cnt[i][c], self.rng.random()))
                if self.cnt[i][q] < self.own(i):
                    self.move(i, q); ch = True

    def nbrs(self, i, c):
        return [w for w in self.adj[i] if self.part[w] == c]

    def walk(self, start, c):
        """Class-c component of `start` (start in class c, degrees <= 2): (vertex list, is_cycle)."""
        nb = self.nbrs(start, c)
        right, prev, cur = [], start, (nb[0] if nb else None)
        while cur is not None:
            if cur == start:
                return [start] + right, True
            right.append(cur)
            nxt = [w for w in self.nbrs(cur, c) if w != prev]
            prev, cur = cur, (nxt[0] if nxt else None)
        left, prev, cur = [], start, (nb[1] if len(nb) > 1 else None)
        while cur is not None:
            left.append(cur)
            nxt = [w for w in self.nbrs(cur, c) if w != prev]
            prev, cur = cur, (nxt[0] if nxt else None)
        return left[::-1] + [start] + right, False

    def is_odd_cycle(self, comp):
        c, cyc = self.walk(comp[0], self.part[comp[0]])
        return cyc and len(c) % 2 == 1 and len(c) == len(comp)

    def odd_cycles(self):
        seen, out = set(), []
        for i in range(self.m):
            if i in seen or self.own(i) != 2:
                continue
            comp, cyc = self.walk(i, self.part[i])
            seen.update(comp)
            if cyc and len(comp) % 2:
                out.append(comp)
        return out

    def delta(self, e, q):
        """Change of #odd cycles if e moves to class q, or None if a class-degree would exceed 2."""
        if q == self.part[e] or self.cnt[e][q] > 2:
            return None
        xs = self.nbrs(e, q)
        if any(self.own(x) >= 2 for x in xs):
            return None
        d = 0
        if self.own(e) == 2:
            comp, cyc = self.walk(e, self.part[e])
            if cyc and len(comp) % 2:
                d -= 1
        if len(xs) == 2:
            comp, cyc = self.walk(xs[0], q)
            if xs[1] in comp and len(comp) % 2 == 0:
                d += 1
        return d


def defects_two_colourable(adj, cycles):
    """SAT: one defect edge per odd cycle, defect conflict graph properly 2-coloured."""
    from pysat.solvers import Solver
    var, cl = {}, []
    for c in cycles:
        lits = []
        for e in c:
            for col in (0, 1):
                var[(e, col)] = len(var) + 1
                lits.append(var[(e, col)])
        cl.append(lits)
    for (e, col), v in var.items():
        for f in adj[e]:
            if (f, col) in var and e < f:
                cl.append([-v, -var[(f, col)]])
    with Solver(name="cd15", bootstrap_with=cl) as s:
        return s.solve()


def run(n, g, seed, steps, p_env=0.3):
    rng = random.Random(seed)
    t0 = time.time()
    G = nx.random_regular_graph(4, n, seed=seed)
    ok = raise_girth(G, g, rng, rounds=200)
    E, adj = conflict_adj(G)
    S = State(adj, rng)
    S.descend()
    high = sum(S.own(i) >= 3 for i in range(S.m))     # possible only for K < 9 (Lovasz needs 9 classes)
    if high:
        return {"n": n, "target girth": g, "girth": nx.girth(G), "seed": seed, "m": len(E),
                "class-degree >= 3 after descent": high, "gen+descent s": round(time.time() - t0, 1)}
    odd = S.odd_cycles()
    res = {"n": n, "target girth": g, "girth": nx.girth(G), "reached": ok, "seed": seed, "m": len(E),
           "odd after descent": len(odd), "lengths after descent": dict(sorted(Counter(map(len, odd)).items())),
           "gen+descent s": round(time.time() - t0, 1)}
    t1, hist, kills, moves = time.time(), [], 0, 0
    for step in range(1, steps + 1):
        if not odd:
            break
        if rng.random() < p_env:
            e = rng.randrange(S.m)
            for q in rng.sample(range(K), K):
                d = S.delta(e, q)
                if d is not None and d <= 0:
                    S.move(e, q); break
        else:
            k = rng.randrange(len(odd))
            if not S.is_odd_cycle(odd[k]):
                odd = S.odd_cycles(); continue
            e = rng.choice(odd[k])
            for q in rng.sample(range(K), K):
                d = S.delta(e, q)
                if d is not None and d <= 0:
                    S.move(e, q)
                    moves += 1
                    if d < 0:
                        kills += 1; odd.pop(k)
                    else:
                        odd[k] = S.walk(e, q)[0]
                    break
        if step % 5000 == 0:
            odd = S.odd_cycles()
            hist.append(len(odd))
    odd = S.odd_cycles()
    assert all(S.own(i) <= 2 for i in range(S.m))
    res.update({"steps": step, "token moves": moves, "token kills": kills, "odd left": len(odd),
                "lengths left": dict(sorted(Counter(map(len, odd)).items())),
                "trace /5000 steps": hist if len(hist) <= 12 else hist[:6] + ["..."] + hist[-4:],
                "search s": round(time.time() - t1, 1)})
    if odd:
        res["defects 2-colourable"] = defects_two_colourable(adj, odd)
    return res


if __name__ == "__main__":
    n, g, seed, steps = map(int, sys.argv[1:5])
    p_env = float(sys.argv[5]) if len(sys.argv) > 5 else 0.3
    K = int(sys.argv[6]) if len(sys.argv) > 6 else 9
    print({"K": K, **run(n, g, seed, steps, p_env)}, flush=True)
