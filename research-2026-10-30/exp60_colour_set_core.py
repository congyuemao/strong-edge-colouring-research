"""exp60: the core criterion for a fixed colour set Y, |Y| = k (NEW_DIRECTIONS 11.26).  The hole walks on colours outside Y only, so the classes of Y never change.
S_Y = edges v not coloured from Y that see every colour of Y and at which every pair of Y is tangled.  tau_Y(v) = 2(20 - k) - deg(v) + d_Y(v).  Peel; h outside the core C_Y gives an insertion.
Each sampled repair is carried out and re-checked by vertex relations.  Usage: exp60_colour_set_core.py k repairs files.json"""
import itertools, json, random, sys
from collections import Counter
from exp33_kempe import K, l2_adj

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

def walk(edges, adj, col0, h, Y, S, rank):
    col = list(col0); v = h; mv = 0
    while True:
        used = Counter(col[y] for y in adj[v] if col[y] >= 0)
        fr = [c for c in range(K) if c not in used]
        if fr:
            col[v] = fr[0]; return col, mv
        if v not in S:
            T = tangled_sets(adj, col)
            for a, b in itertools.combinations(Y, 2):
                if v not in T[a, b]:
                    comp = {}
                    for s in [y for y in adj[v] if col[y] == a]:
                        if s in comp: continue
                        comp[s] = s; st = [s]
                        while st:
                            u = st.pop()
                            for w in adj[u]:
                                if col[w] in (a, b) and w not in comp:
                                    comp[w] = s; st.append(w)
                    for x in comp:
                        col[x] = a if col[x] == b else b
                    assert a not in {col[y] for y in adj[v]}
                    col[v] = a; return col, mv
            raise AssertionError("seed without a separable pair")
        cand = [y for y in adj[v] if col[y] >= 0 and col[y] not in Y and used[col[y]] == 1 and rank.get(y, -1 if y not in S else 10 ** 9) < rank[v]]
        assert cand, "no smaller rank target"
        y = min(cand, key=lambda z: rank.get(z, -1))
        col[v] = col[y]; col[y] = -1; v = y; mv += 1

def check(edges, col):
    nb = {}
    for x, y in edges:
        nb.setdefault(x, set()).add(y); nb.setdefault(y, set()).add(x)
    by = {}
    for i, c in enumerate(col):
        assert c >= 0; by.setdefault(c, []).append(i)
    for L in by.values():
        for i, j in itertools.combinations(L, 2):
            p, q = edges[i]
            assert not (set(edges[i]) & set(edges[j])) and not ((nb[p] | nb[q]) & set(edges[j]))

k = int(sys.argv[1]); reps = int(sys.argv[2]); rng = random.Random(k)
for f in sys.argv[3:]:
    data = json.load(open(f, encoding="utf-8"))
    for x in (data if isinstance(data, list) else [data]):
        edges = [tuple(e) for e in x["edges"]]; h = x["e"]; col = list(x["colouring"]); col[h] = -1
        adj = l2_adj(edges); adjs = [set(r) for r in adj]
        T = tangled_sets(adj, col)
        good = []; tot = 0; big = 0; nontriv = 0; ngood = 0
        for Y in itertools.combinations(range(K), k):
            tot += 1
            cur, rank, S = core(adj, adjs, col, T, Y)
            big = max(big, len(cur))
            nontriv += h in S    # h in S: no pair of Y is separable at h itself, so the repair really needs the walk
            if h not in cur:
                good.append((Y, S, rank))
                ngood += h in S
        mw = 0
        for Y, S, rank in rng.sample(good, min(reps, len(good))):
            new, mv = walk(edges, adj, col, h, Y, S, rank); check(edges, new); mw = max(mw, mv)
        print(f"{x.get('instance','?')}: k={k} good {len(good)}/{tot}; with h tangled on all of Y: good {ngood}/{nontriv}; largest core {big} of {len(edges)}; repairs ok, longest walk {mw}", flush=True)
