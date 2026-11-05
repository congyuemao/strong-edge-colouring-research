import os, random
K = int(os.environ.get("SE_K", "10"))
def l2(edges):
    m = len(edges); adj = [set() for _ in range(m)]
    inc = {}
    for i, (p, q) in enumerate(edges):
        inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i)
    nb = {v: set() for v in inc}
    for p, q in edges:
        nb[p].add(q); nb[q].add(p)
    for i, (p, q) in enumerate(edges):
        s = set(inc[p]) | set(inc[q])
        for w in nb[p] | nb[q]:
            s |= inc[w]
        s.discard(i); adj[i] = s
    return adj
def tabu(adj, skip, rnd, iters=400000):
    m = len(adj); vs = [v for v in range(m) if v != skip]
    col = [rnd.randrange(K) for _ in range(m)]; col[skip] = -1
    gam = [[0] * K for _ in range(m)]
    for v in vs:
        for y in adj[v]:
            if y != skip: gam[v][col[y]] += 1
    tab = {}
    conf = sum(gam[v][col[v]] for v in vs) // 2
    for it in range(iters):
        if conf == 0: return col
        best = None; bd = 10**9
        cand = [v for v in vs if gam[v][col[v]] > 0]
        for v in cand:
            for c in range(K):
                if c == col[v]: continue
                d = gam[v][c] - gam[v][col[v]]
                if tab.get((v, c), -1) >= it and conf + d > 0: continue
                if d < bd or (d == bd and rnd.random() < 0.3): bd = d; best = (v, c)
        if best is None: continue
        v, c = best; o = col[v]; col[v] = c; conf += bd
        tab[(v, o)] = it + rnd.randrange(10) + int(0.6 * len(cand))
        for y in adj[v]:
            if y != skip: gam[y][o] -= 1; gam[y][c] += 1
    return None
