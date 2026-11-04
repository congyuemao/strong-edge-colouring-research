"""exp55: test of the counting core of NEW_DIRECTIONS 11.24 on real finite graphs, by SAT.
Is there a proper 20-colouring of L^2(G) - h and a set R containing h such that
  (a) every x in R sees every colour other than its own (h sees all 20);
  (b) x in R and col[y] single at x imply y in R (y coloured);
  (c) no g, f, w with g in R, f in N(g), w in N(f), g != w, g, w non-conflicting, col[f] single at g, col[w] single at f, col[f] single
      at w?  ((c) would give: move the hole g -> f -> w, then w has the free colour col[f].)
The counting argument predicts UNSAT in any finite graph that is locally a tree; a SAT model refutes the counting argument.  (c) is stated
without the condition that the walk to g avoids f and w, so this is the over-strong form: SAT is decisive, UNSAT only says the
combinatorial core survives.  Option nocond: drop (c) to see what the constraints alone allow.
Usage: exp55_counting_core.py n girth seed edge_index|auto [nocond] [timeout=sec]"""
import itertools, sys, time, threading
import networkx as nx
from pysat.solvers import Cadical195
from graphs_hg import random_girth
from exp33_kempe import l2_adj
K = 20
n, g, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
G = random_girth(n, g, seed) if g > 3 else nx.random_regular_graph(4, n, seed=seed)
edges = [tuple(x) for x in G.edges()]
adj = [set(r) for r in l2_adj(edges)]
m = len(edges)
h = next((i for i in range(m) if len(adj[i]) == 24), 0)
print(f"n={n} girth={nx.girth(G)} seed={seed} m={m} h={h} |N(h)|={len(adj[h])}", flush=True)
top = 0
def new():
    global top
    top += 1
    return top
col = [[new() for c in range(K)] if i != h else None for i in range(m)]
r = [new() for i in range(m)]
sing = {(a, b): new() for a in range(m) for b in adj[a] if b != h}
cl = []
for i in range(m):
    if i == h: continue
    cl.append(col[i][:])
    cl += [[-col[i][a], -col[i][b]] for a, b in itertools.combinations(range(K), 2)]
    for j in adj[i]:
        if j > i and j != h:
            cl += [[-col[i][c], -col[j][c]] for c in range(K)]
cl.append([r[h]])
for a in range(m):
    nb = [z for z in adj[a] if z != h]
    for c in range(K):
        l = [-r[a]] + [col[z][c] for z in nb]
        if a != h: l.append(col[a][c])
        cl.append(l)
    for b in nb:
        others = [z for z in nb if z != b]
        for c in range(K):
            cl.append([-col[b][c], sing[a, b]] + [col[z][c] for z in others])
        cl.append([-r[a], -sing[a, b], r[b]])
if "nocond" not in sys.argv:
    for f in range(m):
        if f == h: continue
        for gg in adj[f]:
            for w in adj[f]:
                if w == gg or w == h or w in adj[gg]: continue
                cl.append([-r[gg], -sing[gg, f], -sing[f, w], -sing[w, f]])
mem = sorted(adj[h])
for pos, f in enumerate(mem):
    for c in range(1, K):
        cl.append([-col[f][c]] + [col[z][c - 1] for z in mem[:pos]])
print(f"vars {top} clauses {len(cl)}", flush=True)
t0 = time.time()
s = Cadical195(bootstrap_with=cl)
ans = s.solve()
print("SAT" if ans else "UNSAT", f"{time.time() - t0:.0f} s", flush=True)
if ans:
    M = set(v for v in s.get_model() if v > 0)
    c = {i: next(a for a in range(K) if col[i][a] in M) for i in range(m) if i != h}
    R = {i for i in range(m) if r[i] in M}
    from collections import Counter
    print("R size", len(R), "of", m)
    ns = []
    for x in R:
        mul = Counter(c[z] for z in adj[x] if z != h)
        ns.append(sum(v for v in mul.values() if v >= 2))
    print("non-single neighbours in R: mean", sum(ns) / len(ns), "max", max(ns))
    import json
    json.dump({"edges": edges, "e": h, "colouring": [c.get(i, -1) for i in range(m)], "R": sorted(R)}, open(f"D:/se20-data/runs/exp55_n{n}_g{g}_s{seed}.json", "w"))
