import itertools
from exp33_kempe import K
def tangled_sets(adj, col):
    m = len(adj); T = {}
    for a, b in itertools.combinations(range(K), 2):
        comp = {}
        for s in range(m):
            if col[s] in (a, b) and s not in comp:
                comp[s] = s; st = [s]
                while st:
                    u = st.pop()
                    for w in adj[u]:
                        if col[w] in (a, b) and w not in comp:
                            comp[w] = s; st.append(w)
        S = set()
        for v in range(m):
            if col[v] in (a, b): continue
            if {comp[y] for y in adj[v] if col[y] == a} & {comp[y] for y in adj[v] if col[y] == b}:
                S.add(v)
        T[a, b] = S
    return T

def core(adj, adjs, col, T, Y):
    S = None
    for p in itertools.combinations(Y, 2):
        S = set(T[p]) if S is None else S & T[p]
    S -= {v for v in S if col[v] in Y}
    tau = {v: 2 * (K - len(Y)) - len(adj[v]) + sum(col[y] in Y for y in adj[v]) for v in S}
    cur = set(S); cnt = {v: len(adjs[v] & cur) for v in cur}
    st = [v for v in cur if cnt[v] < tau[v]]
    rank = {}; r = 0
    while st:
        v = st.pop()
        if v not in cur: continue
        cur.discard(v); rank[v] = r; r += 1
        for y in adjs[v] & cur:
            cnt[y] -= 1
            if cnt[y] < tau[y]: st.append(y)
    return cur, rank, S

