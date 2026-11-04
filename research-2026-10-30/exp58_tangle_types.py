"""exp58: where does non-separability come from?  (NEW_DIRECTIONS 11.26)
For a state phi and an edge v not coloured a, b, the pair (a, b) is tangled at v when an a-neighbour and a b-neighbour of v lie in one (a, b) component.
 D (direct):  some a-neighbour and b-neighbour of v conflict.
 L (long):    tangled, but not D.
Fan lemma: if the conflict cycle v, x, ..., y lies in a tree region, the (a, b) path x...y is inside N(v), so the pair is D.  So L needs a cycle of G.
Checked here: (1) per-edge counts D, L, separable; D <= e(L^2[N(v)]); (2) for every L pair the shortest (a, b) path between an a- and a b-neighbour of v and
whether v + path + connectors contain a cycle of G (independent test of the fan lemma); (3) the rank budget: sum over pairs of (slots - components) = #conflict pairs - excess,
beta = conflict pairs inside components of size >= 3, t = mean number of missing colours per edge, the bound beta <= 5 + t.
Usage: exp58_tangle_types.py files.json  (json: list or dict with edges, e, colouring)"""
import itertools
import json
import sys
from collections import deque

from exp33_kempe import K, l2_adj


def comps(adj, col, a, b):
    comp = {}
    size = {}
    for s in range(len(adj)):
        if col[s] in (a, b) and s not in comp:
            comp[s] = s
            st = [s]
            n = 1
            while st:
                x = st.pop()
                for y in adj[x]:
                    if col[y] in (a, b) and y not in comp:
                        comp[y] = s
                        st.append(y)
                        n += 1
            size[s] = n
    return comp, size


def path(adj, col, a, b, x, ys):
    par = {x: None}
    q = deque([x])
    while q:
        u = q.popleft()
        if u in ys:
            out = [u]
            while par[out[-1]] is not None:
                out.append(par[out[-1]])
            return out[::-1]
        for w in adj[u]:
            if col[w] in (a, b) and w not in par:
                par[w] = u
                q.append(w)
    return None


def has_cycle(edge_ids, edges):
    parent = {}

    def find(x):
        while parent.setdefault(x, x) != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in edge_ids:
        p, q = find(edges[i][0]), find(edges[i][1])
        if p == q:
            return True
        parent[p] = q
    return False


def connectors(edges, nbg, inc, f, g):
    """edges of G through which f, g conflict (empty if they share an endpoint)"""
    if set(edges[f]) & set(edges[g]):
        return []
    out = []
    for p in edges[f]:
        for q in edges[g]:
            if q in nbg[p]:
                out.append(inc[frozenset((p, q))])
    return out[:1]


def main():
    for fn in sys.argv[1:]:
        data = json.load(open(fn, encoding="utf-8"))
        for x in (data if isinstance(data, list) else [data]):
            edges = [tuple(e) for e in x["edges"]]
            h = x.get("e", x.get("hole"))
            col = list(x.get("colouring") or x.get("colours"))
            col[h] = -1
            adj = l2_adj(edges)
            adjs = [set(r) for r in adj]
            m = len(edges)
            nbg = {}
            inc = {}
            for i, (p, q) in enumerate(edges):
                nbg.setdefault(p, set()).add(q)
                nbg.setdefault(q, set()).add(p)
                inc[frozenset((p, q))] = i
            Dtot = Ltot = Stot = 0
            Dmax = 0
            fan_viol = 0
            L_checked = 0
            Lh = Dh = 0
            near = adjs[h]
            beta = pairs_conf = 0
            slots = ncomp = 0
            for a, b in itertools.combinations(range(K), 2):
                comp, size = comps(adj, col, a, b)
                slots += len(comp)
                ncomp += len(size)
                for u in comp:
                    if size[comp[u]] >= 3:
                        beta += sum(1 for w in adj[u] if col[w] in (a, b) and w > u)
                for v in range(m):
                    if v == h or col[v] in (a, b):
                        continue
                    A = [y for y in adj[v] if col[y] == a]
                    B = [y for y in adj[v] if col[y] == b]
                    ca = {comp[y] for y in A}
                    cb = {comp[y] for y in B}
                    if not (ca & cb):
                        Stot += 1
                        continue
                    if any(y in adjs[z] for y in A for z in B):
                        Dtot += 1
                        Dh += v in near
                        continue
                    Ltot += 1
                    Lh += v in near
                    L_checked += 1
                    bs = set(y for y in B if comp[y] in ca)
                    for s in A:
                        if comp[s] in cb:
                            P = path(adj, col, a, b, s, bs)
                            ids = set(P) | {v}
                            seq = [v] + P + [v]
                            for f, g in zip(seq, seq[1:]):
                                ids.update(connectors(edges, nbg, inc, f, g))
                            if not has_cycle(ids, edges):
                                fan_viol += 1
                            break
            for v in range(m):
                if v != h:
                    Dmax = max(Dmax, sum(1 for y, z in itertools.combinations(adj[v], 2) if z in adjs[y]))
            t = sum(1 for v in range(m) if v != h for c in range(K) if c != col[v] and all(col[y] != c for y in adj[v])) / (m - 1)
            mm = m - 1
            print(f"{x.get('instance','?')}: m={m} per edge D={Dtot/mm:.1f} L={Ltot/mm:.1f} sep={Stot/mm:.1f} (of 171); max e(N(v))={Dmax}; "
                  f"near h: D={Dh/24:.1f} L={Lh/24:.1f}; L pairs checked {L_checked}, fan violations {fan_viol}; "
                  f"slots/m={slots/mm:.2f} comps/m={ncomp/mm:.2f} beta/m={beta/mm:.2f} t={t:.2f}", flush=True)


main()
