"""exp47: can conjecture 11.9 be proved from the tree-like ball around e alone?  (NEW_DIRECTIONS 11.17)

Ball: the edges at L2-distance <= 3 from e in the 4-regular tree (2185 edges; these are the edges within vertex distance
6 of e, so the ball is a tree whenever there is no cycle within that distance, e.g. at girth >= 15).  Edges at
distance <= 2 have all 24 conflicts inside the ball; edges at distance 3 (the boundary) may have conflicts outside.

Port relaxation: an (a, b)-component inside the ball that contains a boundary edge may continue outside, so all such
components of one colour pair are treated as linked.  This only adds links, so a pair separable under the relaxation
is separable in every graph containing the ball (a component that never reaches the boundary is a whole component).

Question: is there a partial proper 20-colouring of the ball (edges may stay uncoloured, as in the edge-by-edge
induction; graphs of maximum degree < 4 embed by adding pendant uncoloured edges, which create no new conflicts) with
e blocked, e depth-1 stuck and every singleton member f_p stuck outside p, all under the relaxation?
  UNSAT proves: conjecture 11.9 holds whenever e has no cycle within vertex distance 6 (both for partial and for full
  colourings), hence every graph of maximum degree 4 and girth >= 15 has a strong 20-colouring (insert edge by edge).
  SAT gives a local configuration that any proof has to rule out with structure beyond the ball.

Method (counterexample-guided): start from properness, e blocked and no trivially separable pair at e or at a singleton
member (exp44's T1 / T2), solve, compute the separable pairs of the model under the relaxation, and add for each one a
clause forbidding its certificate: a union K of components that holds all a-members of the centre, no b-member and no
boundary edge.  The certificate is fixed by the colours of K, of the conflicts of K (not a, not b) and of the other
conflicts of the centre (not a); for a member f it also needs f to be the only p-member of N(e).  Every forbidden
colouring really has the separable pair, so the clauses are sound; SAT models are re-checked directly.
Symmetry: near edge i (of the 6 at the ends of e), if coloured, gets a colour <= i (colours renamed by first use).
Mode full: every ball edge except e coloured (the setting of a minimal counterexample, where G - e is coloured).
Usage (run from this directory): exp47_local_proof_cegar.py [max_rounds] [log_dir] [full]
"""
import json
import os
import sys
import time
from collections import Counter
from itertools import combinations

from pysat.solvers import Solver

from exp33_kempe import K, l2_adj
from exp44_local_repair import tree

MAXR = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
LOG = sys.argv[2] if len(sys.argv) > 2 else "."
FULL = "full" in sys.argv[3:]
TAG = "_full" if FULL else ""
t0 = time.time()
edges = tree(6)
adj = l2_adj(edges)
e = 0
dist, layer = {e: 0}, [e]
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
assert len(N) == 24 and all(len(adj[h]) == 24 and set(adj[h]) <= inb for h in ball if dist[h] <= 2)
near = [f for f in N if set(edges[f]) & set(edges[e])]

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
    if FULL:
        add([X[h, c] for c in range(K)])
    for c, d in combinations(range(K), 2):
        add([-X[h, c], -X[h, d]])
    for g in adj[h]:
        if g > h and g in inb and g != e:
            for c in range(K):
                add([-X[h, c], -X[g, c]])
for i, f in enumerate(near):
    for c in range(i + 1, K):
        add([-X[f, c]])
for c in range(K):                                           # e blocked
    add([X[f, c] for f in N])
SEES = {}


def sees(h, c):
    if (h, c) not in SEES:
        v = SEES[h, c] = var()
        add([-v] + [X[g, c] for g in adj[h] if g != e])
    return SEES[h, c]


for p in range(K):                                           # no trivially separable pair at e
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


def z(al, a, b):
    if (al, a, b) not in Z:
        v = Z[al, a, b] = var()
        add([-v, X[al, a]])
        add([-v, sees(al, b)])
    return Z[al, a, b]


def single_lits(f, p):                                       # literals false iff f is the only p-member of N(e)
    return [-X[f, p]] + [X[g, p] for g in N if g != f]


for f in N:                                                  # no trivially separable pair at a singleton member
    nb = [g for g in adj[f] if g != e]
    for p in range(K):
        for a in range(K):
            for b in range(K):
                if len({a, b, p}) == 3:
                    add(single_lits(f, p) + [z(al, a, b) for al in nb])
print(f"ball {len(ball)} edges{' (every edge coloured)' if FULL else ''}; {nv[0]} variables, {ncl[0]} clauses "
      f"[{time.time() - t0:.0f}s]", flush=True)


def separations(col):
    """(centre, p, a, b, K) for every pair separable under the relaxation; p = -1 for e.  K is the certificate side."""
    mult = Counter(col[f] for f in N if col[f] >= 0)
    centres = [(e, -1)] + [(f, col[f]) for f in N if col[f] >= 0 and mult[col[f]] == 1]
    out = []
    for a in range(K):
        for b in range(a + 1, K):
            lab, comps = {}, []
            for st in ball:
                if st in lab or col[st] not in (a, b):
                    continue
                comp, stack = [st], [st]
                lab[st] = len(comps)
                while stack:
                    x = stack.pop()
                    for y in adj[x]:
                        if y in inb and y not in lab and col[y] in (a, b):
                            lab[y] = len(comps)
                            comp.append(y)
                            stack.append(y)
                comps.append(comp)
            out_of = [any(dist[m] == 3 for m in comp) for comp in comps]
            for c, p in centres:
                if p in (a, b):
                    continue
                A = {lab[g] for g in adj[c] if g != e and col[g] == a}
                B = {lab[g] for g in adj[c] if g != e and col[g] == b}
                if A & B or (any(out_of[i] for i in A) and any(out_of[i] for i in B)):
                    continue
                if not any(out_of[i] for i in A) and (any(out_of[i] for i in B) or len(A) <= len(B)):
                    side, x, y = A, a, b
                else:
                    side, x, y = B, b, a
                Kset = set().union(*[set(comps[i]) for i in side]) if side else set()
                out.append((c, p, x, y, Kset))
    return out


def block(c, p, x, y, Kset):
    """clause forbidding the certificate: K keeps its colours, nothing next to K is x / y, no other x-member at c"""
    lits = [-X[h, col_now[h]] for h in Kset]
    rim = {g for h in Kset for g in adj[h] if g not in Kset and g != e}
    lits += [X[g, x] for g in rim] + [X[g, y] for g in rim]
    lits += [X[g, x] for g in adj[c] if g != e and g not in Kset]
    if p >= 0:
        lits += single_lits(c, p)
    add(sorted(set(lits)))


os.makedirs(LOG, exist_ok=True)
hist = []
for rnd in range(1, MAXR + 1):
    ok = s.solve()
    if not ok:
        print(f"round {rnd}: UNSAT [{time.time() - t0:.0f}s] -- no local counterexample: conjecture 11.9 holds when "
              f"e has no cycle within vertex distance 6", flush=True)
        hist.append(("UNSAT", rnd))
        break
    model = set(l for l in s.get_model() if l > 0)
    col_now = [next((c for c in range(K) if X.get((h, c)) in model), -1) if h in inb else -1
               for h in range(len(edges))]
    seps = separations(col_now)
    per = Counter((c, p) for c, p, *_ in seps)
    worst = min((per.get((f, col_now[f]), 0) for f in N if col_now[f] >= 0
                 and sum(col_now[g] == col_now[f] for g in N) == 1), default=None)
    print(f"round {rnd}: {len(seps)} separable (e: {per.get((e, -1), 0)}, singleton members: fewest {worst}, "
          f"most {max((v for (c, p), v in per.items() if p >= 0), default=0)}), "
          f"uncoloured in ball {sum(col_now[h] < 0 for h in ball if h != e)} [{time.time() - t0:.0f}s]", flush=True)
    hist.append((rnd, len(seps)))
    stuck_all = per.get((e, -1), 0) == 0 and not any(p >= 0 for c, p in per)
    if stuck_all:
        print(f"round {rnd}: SAT -- e and every singleton member stuck under the relaxation", flush=True)
        json.dump({"edges": edges, "col": col_now, "ball": ball}, open(f"{LOG}/exp47_witness{TAG}.json", "w"))
        hist.append(("SAT", rnd))
        break
    for t in seps:
        block(*t)
json.dump(hist, open(f"{LOG}/exp47_history{TAG}.json", "w"))
