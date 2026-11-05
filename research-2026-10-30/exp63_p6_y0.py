"""exp63: can the doubled-colour set Y0 fail?  On Codex's P6 graph, keep colours 0, 1 on the C-L edges and ask SAT for a proper colouring of the rest with the other 18 colours in which a chosen L-U edge h is blocked.
Then the doubled colours at h are exactly 0, 1 (three members each), and h is in C_{01} by P6.  Usage: exp63_p6_y0.py graph.json out.json [tries]"""
import itertools, json, sys, time
from pysat.solvers import Cadical195
from exp33_kempe import K, l2_adj
d = json.load(open(sys.argv[1])); edges = [tuple(e) for e in d["edges"]]; col0 = d["colouring"]; m = len(edges)
adj = l2_adj(edges)
pair = (0, 1)
cls = [i for i in range(m) if col0[i] in pair]
print("edges coloured 0, 1:", len(cls))
rest = [i for i in range(m) if col0[i] not in pair or i == d["e"]]
rest = [i for i in rest if i not in cls]
ds = [i for i in rest if sum(col0[y] in pair for y in adj[i]) == 6]
print("rest", len(rest), "edges with six fixed neighbours", len(ds), "degrees", sorted({len(adj[i]) for i in range(m)}))
col18 = list(range(2, K))
for h in ds[:int(sys.argv[3]) if len(sys.argv) > 3 else 3]:
    x = lambda i, c: i * K + c + 1
    s = Cadical195()
    for i in rest:
        if i == h: continue
        s.add_clause([x(i, c) for c in col18])
        for a, b in itertools.combinations(col18, 2): s.add_clause([-x(i, a), -x(i, b)])
        for j in adj[i]:
            if j > i and j in set(rest) and j != h:
                for c in col18: s.add_clause([-x(i, c), -x(j, c)])
    mem = [y for y in adj[h] if y not in cls]
    print("h", h, "members in the 18 colours", len(mem))
    for c in col18: s.add_clause([x(y, c) for y in mem])
    for pos, f in enumerate(mem): s.add_clause([x(f, col18[pos])])   # all distinct: fix by symmetry
    t = time.time(); r = s.solve(); print("SAT" if r else "UNSAT", round(time.time() - t, 1), "s", flush=True)
    if r:
        mdl = set(v for v in s.get_model() if v > 0)
        col = list(col0)
        for i in rest:
            if i != h: col[i] = next(c for c in col18 if x(i, c) in mdl)
        col[h] = -1
        json.dump({"edges": [list(e) for e in edges], "e": h, "colouring": col, "instance": f"p6_h{h}"}, open(sys.argv[2], "w"))
        break
