"""exp77: anatomy of a hard state: for each pair, is h tangled, how big are S_Y and the core, how many peeling steps before h goes, how many N(h) survive, and the types of tangling at h (direct/long).
Usage: exp77_anatomy.py K json out"""
import itertools, json, sys
K = int(sys.argv[1]); x = json.load(open(sys.argv[2])); L = open(sys.argv[3]).read().split()
edges = [tuple(e) for e in x['edges']]; h = x['e']; col = [int(c) for c in L[1:]]; col[h] = -1; m = len(edges)
inc, nb = {}, {}
for i, (p, q) in enumerate(edges):
    inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i); nb.setdefault(p, set()).add(q); nb.setdefault(q, set()).add(p)
adj = []
for i, (p, q) in enumerate(edges):
    s = set(inc[p]) | set(inc[q])
    for w in nb[p] | nb[q]: s |= inc[w]
    s.discard(i); adj.append(s)
print('E', L[0], 'm', m, 'colours at h', sorted(col[f] for f in adj[h]), 'mean free colours', round(sum(sum(1 for c in range(K) if c != col[v] and all(col[y] != c for y in adj[v])) for v in range(m) if v != h) / (m - 1), 2))
rows = []
for a, b in itertools.combinations(range(K), 2):
    comp = {}; size = {}
    for s in range(m):
        if col[s] in (a, b) and s not in comp:
            comp[s] = s; st = [s]; n = 1
            while st:
                u = st.pop()
                for w in adj[u]:
                    if col[w] in (a, b) and w not in comp: comp[w] = s; st.append(w); n += 1
            size[s] = n
    S = {v for v in range(m) if col[v] not in (a, b) and {comp[y] for y in adj[v] if col[y] == a} & {comp[y] for y in adj[v] if col[y] == b}}
    inS = len(S); cur = set(S); order = []
    ch = True; hgone = None
    while ch:
        ch = False
        for v in list(cur):
            if len(adj[v] & cur) < 2 * (K - 2) - len(adj[v]) + sum(col[y] in (a, b) for y in adj[v]):
                cur.discard(v); order.append(v); ch = True
                if v == h: hgone = len(order)
    A = [y for y in adj[h] if col[y] == a]; B = [y for y in adj[h] if col[y] == b]
    direct = any(z in adj[y] for y in A for z in B)
    nh = len(adj[h] & S); need = 2 * (K - 2) - len(adj[h]) + len(A) + len(B)
    rows.append((a, b, h in S, h in cur, inS, len(cur), hgone, nh, need, direct, max(size.values()) if size else 0, len(size)))
print('a b hS hCore |S| |C| hPeeledAt NhS need direct maxComp comps')
for r in rows: print(*r)
import statistics as st
print('good', sum(not r[3] for r in rows), 'of', len(rows), '; h not tangled', sum(not r[2] for r in rows), '; NhS<need among tangled-good', sum(r[2] and not r[3] and r[7] < r[8] for r in rows), '; peeled later', sum(r[2] and not r[3] and r[7] >= r[8] for r in rows))
