"""exp18: check the large-girth construction (matching contraction + Kostochka).

Builds a random graph with max degree 4 and girth >= g, then follows the proof of the
large-girth theorem step by step and verifies every structural claim, then colours the
pieces with SAT and checks the final strong edge colouring uses at most 20 colours.

  1. split E(G) into F1, F2 of max degree 2 (Euler orientation + bipartite split);
  2. D = one edge per odd cycle of F1/F2, pairwise at distance >= SEP (greedy here,
     Haxell's independent-transversal theorem in the proof);
  3. colour F1 - D with {1,2}, F2 - D with {3,4}; M_c = colour class c;
  4. H_c = conflict graph of M_c inside G; claim Delta(H_c) <= 6;
  5. N_D = M_4-edges conflicting with D; dominators J, then I = maximal independent set
     of H_4 - N_D containing J; claim D + I is an induced matching and
     Delta(H[M_4 - I]) <= 5;
  6. colour H_1..H_3 with 5 colours, H[M_4 - I] with 4 colours, D + I with 1 colour.
Kostochka's theorem guarantees step 6 only at girth >= 69; at the small girths we can
afford here SAT finds the colourings anyway, so this checks the assembly logic.
"""
import random
import sys
from collections import defaultdict, deque

from pysat.solvers import Cadical153

SEP = int(sys.argv[4]) if len(sys.argv) > 4 else 8


def random_graph(n, girth, seed):
    """Random greedy graph with max degree 4 and girth >= girth."""
    rng = random.Random(seed)
    adj = [set() for _ in range(n)]
    open_ = list(range(n))
    fails = 0
    while len(open_) > 1 and fails < 20000:
        u, v = rng.sample(open_, 2)
        if v in adj[u] or near(adj, u, v, girth - 2):
            fails += 1
            continue
        adj[u].add(v); adj[v].add(u)
        for w in (u, v):
            if len(adj[w]) == 4:
                open_.remove(w)
    return adj


def near(adj, u, v, r):
    """True if dist(u, v) <= r."""
    seen = {u}; frontier = [u]
    for _ in range(r):
        nxt = []
        for x in frontier:
            for y in adj[x]:
                if y == v:
                    return True
                if y not in seen:
                    seen.add(y); nxt.append(y)
        frontier = nxt
    return False


def girth(adj):
    best = 10 ** 9
    for s in range(len(adj)):
        dist = {s: 0}; par = {s: -1}; q = deque([s])
        while q:
            x = q.popleft()
            if 2 * dist[x] + 1 >= best:
                break
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y:
                    best = min(best, dist[x] + dist[y] + 1)
    return best


def split_two(adj):
    """E(G) = F1 + F2 with max degree <= 2 each (Euler orientation, then bipartite split)."""
    n = len(adj)
    X = n  # dummy vertex joined to odd-degree vertices
    ladj = defaultdict(list)
    eid = 0; ends = {}
    for u in range(n):
        for v in adj[u]:
            if u < v:
                ends[eid] = (u, v); ladj[u].append(eid); ladj[v].append(eid); eid += 1
    real = eid
    for u in range(n):
        if len(adj[u]) % 2:
            ends[eid] = (u, X); ladj[u].append(eid); ladj[X].append(eid); eid += 1
    used = [False] * eid; ptr = defaultdict(int); arcs = []
    for s in list(ladj):
        # Hierholzer, recording each edge in the direction it is traversed
        stack = [(s, None)]
        while stack:
            x, e_in = stack[-1]
            while ptr[x] < len(ladj[x]) and used[ladj[x][ptr[x]]]:
                ptr[x] += 1
            if ptr[x] == len(ladj[x]):
                stack.pop()
                continue
            e = ladj[x][ptr[x]]; used[e] = True
            a, b = ends[e]; y = b if a == x else a
            arcs.append((e, x, y)); stack.append((y, e))
    # bipartite graph out(x) -- in(y); max degree 2, so paths and even cycles: alternate
    out_arcs = defaultdict(list); in_arcs = defaultdict(list)
    for e, x, y in arcs:
        out_arcs[x].append(e); in_arcs[y].append(e)
    head = {e: (x, y) for e, x, y in arcs}
    side = {}
    for e0 in head:
        if e0 in side:
            continue
        # walk the component of the bipartite line structure, alternating sides
        side[e0] = 0; q = [e0]
        while q:
            e = q.pop(); x, y = head[e]
            for f in out_arcs[x] + in_arcs[y]:
                if f != e and f not in side:
                    side[f] = 1 - side[e]; q.append(f)
                elif f != e and side[f] == side[e]:
                    raise RuntimeError("odd cycle in bipartite split")
    F = [[], []]
    for e in range(real):
        F[side[e]].append(ends[e])
    return F


def components(edges):
    """Components of a max-degree-2 edge set: list of (vertex sequence, edge list, is_cycle)."""
    a = defaultdict(list)
    for u, v in edges:
        a[u].append(v); a[v].append(u)
    seen = set(); out = []
    starts = [x for x in a if len(a[x]) == 1] + [x for x in a if len(a[x]) == 2]
    for s in starts:
        if s in seen:
            continue
        seq = [s]; seen.add(s); prev = None; x = s
        while True:
            nxt = [y for y in a[x] if y != prev and y not in seen]
            if not nxt:
                break
            prev, x = x, nxt[0]; seen.add(x); seq.append(x)
        cyc = len(seq) > 2 and seq[0] in a[seq[-1]] and len(a[seq[0]]) == 2
        es = list(zip(seq, seq[1:])) + ([(seq[-1], seq[0])] if cyc else [])
        out.append((seq, es, cyc))
    return out


def ekey(u, v):
    return (u, v) if u < v else (v, u)


def ball(adj, srcs, r):
    dist = {s: 0 for s in srcs}; q = deque(srcs)
    while q:
        x = q.popleft()
        if dist[x] == r:
            continue
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1; q.append(y)
    return dist


def conflict(adj, cls):
    """Conflict graph inside G of a matching cls (list of edges)."""
    at = {}
    for i, (u, v) in enumerate(cls):
        at[u] = i; at[v] = i
    H = [set() for _ in cls]
    for i, (u, v) in enumerate(cls):
        for x in (u, v):
            for t in adj[x]:
                j = at.get(t)
                if j is not None and j != i:
                    H[i].add(j)
    return H


def sat_colour(H, k):
    if not H:
        return []
    s = Cadical153(); var = lambda i, c: i * k + c + 1
    for i in range(len(H)):
        s.add_clause([var(i, c) for c in range(k)])
        for j in H[i]:
            if i < j:
                for c in range(k):
                    s.add_clause([-var(i, c), -var(j, c)])
    if not s.solve():
        return None
    m = set(l for l in s.get_model() if l > 0)
    return [next(c for c in range(k) if var(i, c) in m) for i in range(len(H))]


def run(n, g, seed):
    adj = random_graph(n, g, seed)
    gg = girth(adj)
    m = sum(len(a) for a in adj) // 2
    F = split_two(adj)
    assert all(max((sum(1 for e in Fi if x in e) for x in range(n)), default=0) <= 2 for Fi in F)
    rng = random.Random(seed + 1)
    # D: one edge per odd cycle, pairwise distance >= SEP (greedy)
    D = []; taken = set(); colour = {}
    for j, Fj in enumerate(F):
        for seq, es, cyc in components(Fj):
            if cyc and len(es) % 2:
                cand = es[:]; rng.shuffle(cand)
                pick = next((e for e in cand if not (set(e) & taken)), None)
                if pick is None:
                    return {"seed": seed, "fail": "no separated D-edge"}
                D.append(ekey(*pick)); taken |= set(ball(adj, list(pick), SEP - 1))
                i = es.index(pick); es = es[i + 1:] + es[:i]  # path after removing pick
            for t, e in enumerate(es):
                colour[ekey(*e)] = 2 * j + (t % 2) + 1
    Dset = set(D)
    assert len(colour) + len(D) == m
    M = {c: [e for e, cc in colour.items() if cc == c] for c in (1, 2, 3, 4)}
    for c in M:  # proper: each M_c a matching
        vs = [x for e in M[c] for x in e]; assert len(vs) == len(set(vs)), c
    H = {c: conflict(adj, M[c]) for c in M}
    maxdeg = {c: max((len(h) for h in H[c]), default=0) for c in H}
    assert all(d <= 6 for d in maxdeg.values()), maxdeg
    # N_D, dominators J, maximal independent I
    near_D = set(x for e in D for x in ball(adj, list(e), 1))
    M4 = M[4]; H4 = H[4]
    ND = {i for i, (u, v) in enumerate(M4) if u in near_D or v in near_D}
    J = set(); blocked = set(ND)
    for i in sorted(ND):
        if len(H4[i]) < 6 or H4[i] & J:
            continue
        d = next((j for j in sorted(H4[i]) if j not in blocked and not (H4[j] & J)), None)
        if d is None:
            return {"seed": seed, "fail": "no dominator", "girth": gg}
        J.add(d)
    I = set(J)
    for i in rng.sample(range(len(M4)), len(M4)):
        if i not in ND and i not in I and not (H4[i] & I):
            I.add(i)
    # checks
    R = D + [M4[i] for i in I]
    vs = [x for e in R for x in e]; assert len(vs) == len(set(vs)), "R not a matching"
    Rv = set(vs); owner = {x: k for k, e in enumerate(R) for x in e}
    for k, (u, v) in enumerate(R):
        for x in (u, v):
            for t in adj[x]:
                assert owner.get(t, k) == k, "R not induced"
    rest = [i for i in range(len(M4)) if i not in I]
    K = [M4[i] for i in rest]; HK = conflict(adj, K)
    dK = max((len(h) for h in HK), default=0)
    assert dK <= 5, dK
    # colour and assemble
    final = {}; off = 0
    for c, k in ((1, 5), (2, 5), (3, 5)):
        col = sat_colour(H[c], k)
        if col is None:
            return {"seed": seed, "fail": f"H_{c} not 5-colourable"}
        for e, x in zip(M[c], col):
            final[e] = off + x
        off += k
    col = sat_colour(HK, 4)
    if col is None:
        return {"seed": seed, "fail": "H[M4-I] not 4-colourable"}
    for e, x in zip(K, col):
        final[e] = off + x
    off += 4
    for e in R:
        final[ekey(*e)] = off
    off += 1
    assert len(final) == m and off == 20
    # verify strong edge colouring
    for (u, v), c in final.items():
        for x in (u, v):
            for y in adj[x]:
                f = ekey(x, y)
                if f != (u, v):
                    assert final[f] != c
                for z in adj[y]:
                    f2 = ekey(y, z)
                    if f2 != (u, v):
                        assert final[f2] != c, ((u, v), f2)
    deg4 = sum(1 for a in adj if len(a) == 4)
    return {"seed": seed, "n": n, "m": m, "deg4": deg4, "girth": gg, "odd_cycles": len(D),
            "maxdeg_H": maxdeg, "N_D": len(ND), "J": len(J), "I": len(I),
            "maxdeg_H[M4-I]": dK, "colours": off, "ok": True}


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    g = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    seeds = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    for s in range(seeds):
        print(run(n, g, s), flush=True)
