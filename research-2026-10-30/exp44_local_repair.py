"""exp44: can a blocked edge always be inserted by a few single-edge recolourings when its neighbourhood is a tree?

Local repairs (no Kempe chains; NEW_DIRECTIONS 11.15):
  T1  some colour p and some q != p with every p-member of N(e) missing q: recolour them all to q, colour e with p;
  T2  a singleton colour p, colours a, b outside p with every a-neighbour of f_p missing b: recolour those to b,
      f_p to a, colour e with p (theorem 11.7 with a trivial round, all neighbours of one colour at once).
SAT on the 4-regular tree around e, on the edges at L2-distance <= 3 from e: is there a (partial) proper 20-colouring
with e blocked and neither T1 nor T2 available?  UNSAT would have proved: when that ball is a tree, every blocked edge
is insertable by at most 7 single-edge recolourings.  Result: SAT, also in mode weak (2185 edges, 2.5 min and 17 s with
cadical; both witnesses re-checked independently), so no local repair within two levels proves insertion at any
girth.  Colours of the near clique are fixed to 0..5 (symmetry).
Weak forms (mode weak): T1' some colour p whose members of N(e) can each be recoloured (each to a colour it misses;
same-coloured edges never conflict, so all at once), then e gets p; T2' a singleton p and a colour a != p such that every
a-neighbour of f_p can be recoloured, then f_p gets a and e gets p.  Not T1' / T2' means: some member of each colour
of N(e) is saturated, and for every singleton p and a != p some a-neighbour of f_p is saturated.
Usage: exp44_local_repair.py [full] [weak]   (full: every edge of the ball coloured; default allows uncoloured edges)
"""
import sys
import time
from itertools import combinations

from pysat.solvers import Solver

from exp33_kempe import K, l2_adj


def tree(depth):
    edges, frontier, nxt = [(0, 1)], [0, 1], 2
    deg = {0: 1, 1: 1}
    for _ in range(depth):
        new = []
        for x in frontier:
            while deg[x] < 4:
                edges.append((x, nxt))
                deg[x] += 1
                deg[nxt] = 1
                new.append(nxt)
                nxt += 1
        frontier = new
    return edges


def main(full, weak):
    t0 = time.time()
    edges = tree(6)
    adj = l2_adj(edges)
    e = 0
    dist = {e: 0}
    layer = [e]
    for d in (1, 2, 3):
        nl = []
        for h in layer:
            for g in adj[h]:
                if g not in dist:
                    dist[g] = d
                    nl.append(g)
        layer = nl
    ball = sorted(dist)
    inb = set(ball)
    N = adj[e]
    assert len(N) == 24 and all(len(adj[h]) == 24 for h in ball if dist[h] <= 2)
    print(f"ball: {len(ball)} edges (L2-distance <= 3), {sum(dist[h] <= 2 for h in ball)} within distance 2", flush=True)
    s = Solver(name="cadical195")
    nv = [0]

    def var():
        nv[0] += 1
        return nv[0]

    X = {(h, c): var() for h in ball if h != e for c in range(K)}
    ncl = [0]

    def add(cl):
        s.add_clause(cl)
        ncl[0] += 1

    for h in ball:
        if h == e:
            continue
        if full:
            add([X[h, c] for c in range(K)])
        for c, d in combinations(range(K), 2):
            add([-X[h, c], -X[h, d]])
        for g in adj[h]:
            if g > h and g in inb and g != e:
                for c in range(K):
                    add([-X[h, c], -X[g, c]])
    near = [f for f in N if set(edges[f]) & set(edges[e])]
    for i, f in enumerate(near):
        add([X[f, i]])
    for c in range(K):                                       # e blocked
        add([X[f, c] for f in N])
    SEES = {}

    def sees(h, c):                                          # h has a c-coloured neighbour (one direction suffices)
        if (h, c) not in SEES:
            v = SEES[h, c] = var()
            add([-v] + [X[g, c] for g in adj[h] if g != e])
        return SEES[h, c]

    SAT = {}

    def sat(h, c):                                           # h is c-coloured and sees all other colours
        if (h, c) not in SAT:
            v = SAT[h, c] = var()
            add([-v, X[h, c]])
            for q in range(K):
                if q != c:
                    add([-v, sees(h, q)])
        return SAT[h, c]

    if weak:
        for p in range(K):                                   # no T1': some p-member of N(e) is saturated
            add([sat(f, p) for f in N])
        for f in N:                                          # no T2': some a-neighbour of a singleton f is saturated
            nb = [g for g in adj[f] if g != e]
            for p in range(K):
                single = [-X[f, p]] + [X[g, p] for g in N if g != f]
                for a in range(K):
                    if a != p:
                        add(single + [sat(al, a) for al in nb])
    for p in range(K if not weak else 0):                    # no T1
        for q in range(K):
            if q != p:
                lits = []
                for f in N:
                    t = var()
                    add([-t, X[f, p]])
                    add([-t, sees(f, q)])
                    lits.append(t)
                add(lits)
    Z = {}

    def z(al, a, b):                                         # al is a-coloured and sees b
        if (al, a, b) not in Z:
            v = Z[al, a, b] = var()
            add([-v, X[al, a]])
            add([-v, sees(al, b)])
        return Z[al, a, b]

    for f in (N if not weak else []):                        # no T2 at a singleton member f
        nb = [g for g in adj[f] if g != e]
        for p in range(K):
            single = [-X[f, p]] + [X[g, p] for g in N if g != f]
            for a in range(K):
                for b in range(K):
                    if len({a, b, p}) == 3:
                        add(single + [z(al, a, b) for al in nb])
    print(f"{nv[0]} variables, {ncl[0]} clauses [{time.time() - t0:.0f}s]; solving", flush=True)
    r = s.solve()
    print("blocked, no T1, no T2:", "SAT" if r else "UNSAT", f"[{time.time() - t0:.0f}s]", flush=True)
    if r:
        model = set(l for l in s.get_model() if l > 0)
        col = [next((c for c in range(K) if X.get((h, c)) in model), -1) if h in inb else -1 for h in range(len(edges))]
        unc = sum(col[h] < 0 for h in ball if h != e)
        print("uncoloured edges in the ball:", unc)
        return edges, col, dist
    return None


if __name__ == "__main__":
    main("full" in sys.argv[1:], "weak" in sys.argv[1:])
