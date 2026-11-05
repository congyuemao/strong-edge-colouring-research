"""exp66_check: independent recheck of Delta = 3 states.  Reads <tag>.json and a .out file (energy, colours).
Prints: proper?, colours at h, separable pairs at h, one-layer sum (edge, separable pair) over N(h), and for k = 2..: good sets / all sets, sets with h tangled, largest core.
Usage: exp66_check.py K tag.json file.out [kmax]"""
import itertools, json, sys
K = int(sys.argv[1])
def l2(edges):
    m = len(edges); inc = {}; nb = {}
    for i, (p, q) in enumerate(edges):
        inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i)
        nb.setdefault(p, set()).add(q); nb.setdefault(q, set()).add(p)
    adj = []
    for i, (p, q) in enumerate(edges):
        s = set(inc[p]) | set(inc[q])
        for w in nb[p] | nb[q]: s |= inc[w]
        s.discard(i); adj.append(s)
    return adj
def tangled(adj, col):
    m = len(adj); T = {}
    for a, b in itertools.combinations(range(K), 2):
        comp = {}
        for s in range(m):
            if col[s] in (a, b) and s not in comp:
                comp[s] = s; st = [s]
                while st:
                    u = st.pop()
                    for w in adj[u]:
                        if col[w] in (a, b) and w not in comp: comp[w] = s; st.append(w)
        S = set()
        for v in range(m):
            if col[v] in (a, b): continue
            if {comp[y] for y in adj[v] if col[y] == a} & {comp[y] for y in adj[v] if col[y] == b}: S.add(v)
        T[a, b] = S
    return T
def core(adj, col, T, Y):
    S = None
    for p in itertools.combinations(Y, 2): S = set(T[p]) if S is None else S & T[p]
    S -= {v for v in S if col[v] in Y}
    cur = set(S)
    ch = True
    while ch:
        ch = False
        for v in list(cur):
            need = 2 * (K - len(Y)) - len(adj[v]) + sum(col[y] in Y for y in adj[v])
            if len(adj[v] & cur) < need: cur.discard(v); ch = True
    return cur, S
x = json.load(open(sys.argv[2])); edges = [tuple(e) for e in x["edges"]]; h = x["e"]; adj = l2(edges)
L = open(sys.argv[3]).read().split(); E = int(L[0]); col = [int(c) for c in L[1:]]; col[h] = -1
bad = sum(1 for v in range(len(adj)) for y in adj[v] if col[v] >= 0 and col[v] == col[y])
T = tangled(adj, col)
nbh = sorted(adj[h]); seen = {col[f] for f in nbh}
hsep = sum(h not in T[p] for p in T)
tot = sum(1 for p in T for f in nbh if col[f] not in p and f not in T[p])
print(f"{x['instance']} {sys.argv[3].rsplit('/',1)[-1]}: E={E} m={len(adj)} deg h={len(nbh)} improper={bad} colours at h={len(seen)}/{K} sep at h={hsep}; sum sep={tot} threshold={(K*(K-1)//2*(2*K-2*2-len(nbh))+(K-1)*len(nbh))}->sumT need; sumT={sum(1 for p in T for f in nbh if f in T[p])}", flush=True)
kmax = int(sys.argv[4]) if len(sys.argv) > 4 else K - 1
for k in range(2, kmax + 1):
    good = tot2 = ht = 0; mx = 0
    for Y in itertools.combinations(range(K), k):
        C, S = core(adj, col, T, Y); tot2 += 1; ht += h in S; good += h not in C; mx = max(mx, len(C))
    print(f"   k={k}: good {good}/{tot2}, h tangled on all of Y in {ht}, of those good {ht-(tot2-good)}, largest core {mx}", flush=True)
