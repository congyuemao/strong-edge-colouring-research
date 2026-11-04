"""exp50b: remove the edges on triangles (always insertable, lemma 11.17), then peel L^2 down to degree >= 20.  A graph with an
empty core has chi'_s <= 20 by theorem 11.39 / corollary 11.40 of NEW_DIRECTIONS 11.23.  Also runs the insertion itself:
colour the non-triangle edges greedily in reverse peeling order, then insert the triangle edges by lemma 11.17 on every
graph with an empty core, and checks the final colouring with vertex relations only.
Usage: exp50b_triangle_core.py n [limit]"""
import random
import sys
from exp33_kempe import l2_adj, load
K = 20
def analyse(edges, check, rng):
    adj = [set(r) for r in l2_adj(edges)]
    m = len(edges)
    nb = {}
    for a, b in edges:
        nb.setdefault(a, set()).add(b)
        nb.setdefault(b, set()).add(a)
    tri = [bool(nb[a] & nb[b]) for a, b in edges]
    # plain core, for comparison
    def core(alive):
        alive = set(alive)
        order = []
        ch = True
        while ch:
            ch = False
            for f in list(alive):
                if len(adj[f] & alive) <= 19:
                    alive.discard(f)
                    order.append(f)
                    ch = True
        return alive, order
    c0, _ = core(range(m))
    c1, order = core(f for f in range(m) if not tri[f])
    ok = None
    if check and not c1:
        col = [-1] * m
        for f in reversed(order):
            used = {col[g] for g in adj[f]}
            col[f] = rng.choice([c for c in range(K) if c not in used])
        ts = [f for f in range(m) if tri[f]]
        rng.shuffle(ts)
        for e in ts:
            used = [col[g] for g in adj[e] if col[g] >= 0]
            fr = [c for c in range(K) if c not in used]
            if not fr:
                done = False
                for g in adj[e]:
                    if col[g] >= 0 and used.count(col[g]) == 1:
                        q = [c for c in range(K) if c != col[g] and c not in {col[h] for h in adj[g]}]
                        if q:
                            p = col[g]
                            col[g] = q[0]
                            col[e] = p
                            done = True
                            break
                assert done, "lemma 11.17 failed"
            else:
                col[e] = rng.choice(fr)
        ends = [set(x) for x in edges]
        for i in range(m):
            assert col[i] >= 0
            for j in range(i + 1, m):
                if col[i] == col[j]:
                    a, b = edges[i]
                    assert not (ends[i] & ends[j]) and not ((nb[a] | nb[b]) & ends[j]), (i, j)
        ok = True
    return len(c0), len(c1), sum(tri), ok
n = int(sys.argv[1])
limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
rng = random.Random(n)
gs = list(load(n))
if limit:
    rng.shuffle(gs)
    gs = gs[:limit]
tot = len(gs)
c0n = c1n = chk = 0
tri_all = 0
rest = []
for i, edges in enumerate(gs):
    a, b, t, ok = analyse(edges, True, rng)
    c0n += a > 0
    c1n += b > 0
    chk += bool(ok)
    tri_all += t == len(edges)
    if b:
        rest.append((i, a, b, t))
print(f"n={n}: {tot} graphs; non-empty L^2 core {c0n}; non-empty core after removing triangle edges {c1n}; colourings built and checked {chk}; all edges on triangles {tri_all}")
print("surviving (graph index, plain core, new core, triangle edges):", rest[:12])
