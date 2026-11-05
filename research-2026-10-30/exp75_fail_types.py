"""exp75: which colour pairs fail?  For each end state (json + .out) list, for failing pairs Y (h in C_Y), the type: number of colours of Y on near edges of h (sharing an endpoint with h), d_Y(h).
Usage: exp75_fail_types.py K json out [json out ...]"""
import itertools, json, sys, collections
K = int(sys.argv[1]); tot = collections.Counter(); fail = collections.Counter(); 
def l2(edges):
    inc, nb = {}, {}
    for i, (p, q) in enumerate(edges):
        inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i); nb.setdefault(p, set()).add(q); nb.setdefault(q, set()).add(p)
    adj = []
    for i, (p, q) in enumerate(edges):
        s = set(inc[p]) | set(inc[q])
        for w in nb[p] | nb[q]: s |= inc[w]
        s.discard(i); adj.append(s)
    return adj
args = sys.argv[2:]; nst = 0
for jf, of in zip(args[::2], args[1::2]):
    x = json.load(open(jf)); edges = [tuple(e) for e in x['edges']]; h = x['e']; adj = l2(edges); m = len(edges)
    L = open(of).read().split(); col = [int(c) for c in L[1:]]; col[h] = -1
    near = [f for f in adj[h] if set(edges[f]) & set(edges[h])]
    nearc = {col[f] for f in near}
    ok = len({col[f] for f in adj[h]}) == K
    nfail = 0
    for a, b in itertools.combinations(range(K), 2):
        comp = {}
        for s in range(m):
            if col[s] in (a, b) and s not in comp:
                comp[s] = s; st = [s]
                while st:
                    u = st.pop()
                    for w in adj[u]:
                        if col[w] in (a, b) and w not in comp: comp[w] = s; st.append(w)
        S = {v for v in range(m) if col[v] not in (a, b) and {comp[y] for y in adj[v] if col[y] == a} & {comp[y] for y in adj[v] if col[y] == b}}
        cur = set(S); ch = True
        while ch:
            ch = False
            for v in list(cur):
                if len(adj[v] & cur) < 2 * (K - 2) - len(adj[v]) + sum(col[y] in (a, b) for y in adj[v]): cur.discard(v); ch = True
        t = (len({a, b} & nearc), sum(col[y] in (a, b) for y in adj[h]))
        tot[t] += 1
        if h in cur: fail[t] += 1; nfail += 1
    nst += 1
print('states', nst)
print('(near colours in Y, d_Y(h)) : failing / total')
for t in sorted(tot): print(t, fail[t], '/', tot[t])
