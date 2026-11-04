"""exp59: necessary conditions if every colour pair fails at (h, phi) (NEW_DIRECTIONS 11.26), measured on real states:
   h tangled pairs (190 needed), sum over f in N(h) of tangled(f) against 190*(36-deg h) + 19*deg h, saturation of the singles, d_ab <= deg - 18 on the core,
   and forward degree >= 2 in the core when the ball is a tree.  Usage: exp59_core_shape.py files.json"""
import itertools, json, sys
from exp33_kempe import K, l2_adj
for fn in sys.argv[1:]:
    data = json.load(open(fn, encoding="utf-8"))
    for x in (data if isinstance(data, list) else [data]):
        edges = [tuple(e) for e in x["edges"]]
        h = x.get("e", x.get("hole"))
        col = list(x.get("colouring") or x.get("colours")); col[h] = -1
        adj = l2_adj(edges); adjs = [set(r) for r in adj]
        m = len(edges)
        tang = [0] * m
        tangh = 0
        fail = 0
        dmax = 0
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
                    S.add(v); tang[v] += 1
            tangh += h in S
            d = {v: sum(col[y] in (a, b) for y in adj[v]) for v in S}
            tau = {v: 36 - len(adj[v]) + d[v] for v in S}
            cur = set(S); cnt = {v: len(adjs[v] & cur) for v in cur}
            st = [v for v in cur if cnt[v] < tau[v]]
            while st:
                v = st.pop()
                if v not in cur: continue
                cur.discard(v)
                for y in adjs[v] & cur:
                    cnt[y] -= 1
                    if cnt[y] < tau[y]: st.append(y)
            if h in cur:
                fail += 1
                dmax = max(dmax, max(d[v] - (len(adj[v]) - 18) for v in cur))
                assert all(cnt[v] >= tau[v] for v in cur)
        dh = len(adj[h])
        need = 190 * (36 - dh) + 19 * dh
        sumT = sum(tang[f] for f in adj[h])
        sing = [f for f in adj[h] if sum(col[z] == col[f] for z in adj[h]) == 1]
        sat = sum(len({col[y] for y in adj[f] if y != h}) == 19 for f in sing)
        print(f"{x.get('instance','?')}: fail {fail}/190 tangled at h {tangh}/190; sum T(f) {sumT} need {need} (deg {dh}); singles {len(sing)} saturated {sat}; on fail cores d-(deg-18) max {dmax}", flush=True)
