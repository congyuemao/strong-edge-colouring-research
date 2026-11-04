"""exp56: the two-colour core criterion (NEW_DIRECTIONS 11.25, due to the Codex report), written independently of Codex's code.
Fix colours a, b.  S_ab = edges not coloured a, b at which (a, b) is not separable (a missing colour counts as separable).
tau(v) = 2 * 18 - deg(v) + d_ab(v), d_ab(v) = number of neighbours coloured a, b, deg(v) = conflicts in the whole graph minus the hole.
Delete from S_ab, repeatedly, any v with fewer than tau(v) neighbours in the current set; C_ab is what remains.
If h is outside C_ab, walk: at hole v, if a colour is free, fill; if v is outside S_ab, swap the (a, b) components meeting its a-neighbours and fill
a; else move to a neighbour of smaller rank whose colour (not a, b) is single at v.  Every repair is carried out and the final colouring re-checked with
vertex relations only.  Usage: exp56_pair_core.py [repairs_per_state] files...   (json: edges, e or hole, colouring)"""
import json, random, sys, itertools
from collections import Counter
from exp33_kempe import K, l2_adj

def analyse(adj, col, h, a, b):
    m = len(adj)
    comp = {}
    for s in range(m):
        if col[s] in (a, b) and s not in comp:
            comp[s] = s
            st = [s]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if col[y] in (a, b) and y not in comp:
                        comp[y] = s
                        st.append(y)
    S = set()
    for v in range(m):
        if col[v] in (a, b):
            continue
        ca = {comp[y] for y in adj[v] if col[y] == a}
        cb = {comp[y] for y in adj[v] if col[y] == b}
        if ca & cb:
            S.add(v)
    return comp, S

def core(adj, col, S, h, a, b):
    rank = {}
    cur = set(S)
    tau = {}
    for v in S:
        d = sum(col[y] in (a, b) for y in adj[v])
        deg = len(adj[v])   # at a later hole v every other edge, h included, is coloured
        tau[v] = 2 * (K - 2) - deg + d
    cnt = {v: len(adj_set[v] & cur) for v in cur}
    st = [v for v in cur if cnt[v] < tau[v]]
    r = 0
    while st:
        v = st.pop()
        if v not in cur:
            continue
        cur.discard(v)
        rank[v] = r
        r += 1
        for y in adj_set[v] & cur:
            cnt[y] -= 1
            if cnt[y] < tau[y]:
                st.append(y)
    return cur, rank

def repair(edges, adj, col0, h, a, b, S, rank):
    col = list(col0)
    v = h
    moves = 0
    while True:
        used = Counter(col[y] for y in adj[v] if col[y] >= 0)
        fr = [c for c in range(K) if c not in used]
        if fr:
            col[v] = fr[0]
            return col, moves, "free"
        if v not in S:
            comp, _ = analyse(adj, col, -1, a, b)
            sw = {comp[y] for y in adj[v] if col[y] == a}
            assert not sw & {comp[y] for y in adj[v] if col[y] == b}
            for x in range(len(adj)):
                if col[x] in (a, b) and comp[x] in sw:
                    col[x] = a if col[x] == b else b
            assert a not in {col[y] for y in adj[v]}
            col[v] = a
            return col, moves, "swap"
        cand = [y for y in adj[v] if col[y] not in (a, b, -1) and used[col[y]] == 1 and rank.get(y, -1 if y not in S else 10 ** 9) < rank[v]]
        assert cand, "no smaller rank target"
        y = min(cand, key=lambda z: rank.get(z, -1))
        col[v] = col[y]
        col[y] = -1
        v = y
        moves += 1

def check(edges, col):
    nb = {}
    for x, y in edges:
        nb.setdefault(x, set()).add(y)
        nb.setdefault(y, set()).add(x)
    bycol = {}
    for i, c in enumerate(col):
        assert c >= 0
        bycol.setdefault(c, []).append(i)
    for c, L in bycol.items():
        for i, j in itertools.combinations(L, 2):
            p, q = edges[i]
            assert not (set(edges[i]) & set(edges[j])) and not ((nb[p] | nb[q]) & set(edges[j])), (i, j)

reps = int(sys.argv[1])
rng = random.Random(1)
tot = {"states": 0, "repairs": 0}
low = 999
print("state | hole blocked | pairs with h outside C_ab | largest core | largest walk")
for f in sys.argv[2:]:
    d = json.load(open(f, encoding="utf-8"))
    for x in (d if isinstance(d, list) else [d]):
        edges = [tuple(e) for e in x["edges"]]
        h = x.get("e", x.get("hole"))
        col = list(x.get("colouring") or x.get("colours"))
        col[h] = -1
        adj = l2_adj(edges)
        adj_set = [set(r) for r in adj]
        good = []
        big = 0
        for a, b in itertools.combinations(range(K), 2):
            comp, S = analyse(adj, col, h, a, b)
            cur, rank = core(adj, col, S, h, a, b)
            big = max(big, len(cur))
            if h not in cur:
                good.append((a, b, S, rank))
        tot["states"] += 1
        low = min(low, len(good))
        mw = 0
        for a, b, S, rank in rng.sample(good, min(reps, len(good))):
            new, mv, kind = repair(edges, adj, col, h, a, b, S, rank)
            check(edges, new)
            tot["repairs"] += 1
            mw = max(mw, mv)
        print(x.get("instance", f[-28:])[:40], len({col[y] for y in adj[h]}) == K, len(good), big, mw, flush=True)
print(tot, "fewest good pairs", low)
