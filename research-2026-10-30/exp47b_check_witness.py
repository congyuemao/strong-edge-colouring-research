"""exp47b: independent check of an exp47 witness, from the edge list and the colouring alone (conflicts from the vertex
sets, distances and components recomputed here; no exp33 / exp47 code).
Checks: the colouring of the ball is proper; e is uncoloured and blocked; under the port relaxation (components that
contain an edge at L2-distance 3 from e, or R for a ball of radius R, are linked) e is depth-1 stuck and every singleton member f_p is stuck outside p.
Usage: exp47b_check_witness.py <witness.json>
"""
import json
import sys
from collections import Counter, deque

w = json.load(open(sys.argv[1], encoding="utf-8"))
edges, col = [tuple(x) for x in w["edges"]], w["col"]
K, e, m = 20, 0, len(edges)
nb = {}
for x, y in edges:
    nb.setdefault(x, set()).add(y)
    nb.setdefault(y, set()).add(x)
inc = {}
for i, (x, y) in enumerate(edges):
    inc.setdefault(x, []).append(i)
    inc.setdefault(y, []).append(i)
conf = []
for i, (x, y) in enumerate(edges):
    near = {x, y} | nb[x] | nb[y]                 # an edge conflicts with i iff it has an endpoint in N[x] or N[y]
    conf.append(sorted({j for v in near for j in inc[v]} - {i}))
dist = {e: 0}
q = deque([e])
while q:
    h = q.popleft()
    for g in conf[h]:
        if g not in dist:
            dist[g] = dist[h] + 1
            q.append(g)
R = max(dist.values())                            # the boundary: L2-distance 3, or R for a ball of radius R
ball = [h for h in range(m) if dist[h] <= R]
assert len(ball) == m and sorted(ball) == sorted(w["ball"])
assert col[e] == -1 and all(-1 <= c < K for c in col)
bad = sum(col[i] >= 0 and col[i] == col[j] for i in ball for j in conf[i] if j > i)
N = conf[e]
mult = Counter(col[f] for f in N if col[f] >= 0)
print(f"ball {len(ball)} edges, {sum(col[h] < 0 for h in ball) - 1} uncoloured besides e; improper pairs {bad}; "
      f"|N(e)| = {len(N)}, colours on N(e) {len(mult)}, singletons {sum(v == 1 for v in mult.values())}")


def links(a, b):
    lab = {}
    for s in ball:
        if s in lab or col[s] not in (a, b):
            continue
        comp, stack = [s], [s]
        lab[s] = s
        while stack:
            x = stack.pop()
            for y in conf[x]:
                if y not in lab and col[y] in (a, b):
                    lab[y] = s
                    comp.append(y)
                    stack.append(y)
        if any(dist[c] == R for c in comp):
            for c in comp:
                lab[c] = "outside"
    return lab


lab = {(a, b): links(a, b) for a in range(K) for b in range(a + 1, K)}


def separable_pairs(c, excl):
    out = 0
    for (a, b), L in lab.items():
        if excl in (a, b):
            continue
        A = {L[g] for g in conf[c] if col[g] == a}
        B = {L[g] for g in conf[c] if col[g] == b}
        out += not (A & B)
    return out


se = separable_pairs(e, -2)
singles = [(p, next(f for f in N if col[f] == p)) for p in range(K) if mult[p] == 1]
sp = {p: separable_pairs(f, p) for p, f in singles}
print(f"separable at e under the relaxation: {se}; at the singleton members: {sorted(sp.values())}")
ok = bad == 0 and len(mult) == K and se == 0 and all(v == 0 for v in sp.values())
print("WITNESS OK: proper, e blocked and stuck, every singleton member stuck outside its colour" if ok else "NOT A WITNESS")
