"""exp21: property P -- a 5-edge-colouring in which every edge sees its own colour missing nearby.

Property P for a proper 5-edge-colouring M_1..M_5 of G:
  every edge e of colour c has at most 5 outer neighbours covered by M_c
(outer neighbours of e = uv: (N(u) u N(v)) - {u, v}).  With girth(G) >= 69 this gives
Delta(H(M_c)) <= 5 and girth(H(M_c)) >= 35, so Kostochka's Corollary 2 colours each H(M_c) with
4 colours: chi'_s(G) <= 5 * 4 = 20, with no sparse defect set needed (LARGE_GIRTH section 9).

SAT encoding: x(e,c) edge colours (proper); miss(w,c) -> no edge at w has colour c (the helper is
only used positively, so the implication in this direction is the sound one); for every edge e with
6 outer neighbours and every c:  not x(e,c)  or  OR_{w outer} miss(w,c).

Modes
  small N          all connected quartic graphs on 5..N vertices (graphs_n*.txt)
  girth N          the same graphs: failures broken down by (n, girth)
  random n g s     s random graphs with max degree 4 and girth >= g (exp18_large_girth.random_graph)
"""
import multiprocessing as mp
import sys
import time

from pysat.solvers import Cadical153


def load(n):
    with open(f"graphs_n{n}.txt") as fh:
        for line in fh:
            yield [tuple(map(int, t.split("-"))) for t in line.split()]


def property_p(edges, k=5, budget=None):
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    E = [tuple(sorted(e)) for e in edges]
    m = len(E)
    verts = sorted(adj); vid = {v: i for i, v in enumerate(verts)}
    at = {v: [] for v in verts}
    for i, (u, v) in enumerate(E):
        at[u].append(i); at[v].append(i)
    x = lambda e, c: 1 + e * k + c
    miss = lambda w, c: 1 + m * k + vid[w] * k + c
    s = Cadical153()
    for e in range(m):
        s.add_clause([x(e, c) for c in range(k)])
    for v in verts:
        es = at[v]
        for i in range(len(es)):
            for j in range(i + 1, len(es)):
                for c in range(k):
                    s.add_clause([-x(es[i], c), -x(es[j], c)])
        for c in range(k):
            for f in es:
                s.add_clause([-miss(v, c), -x(f, c)])
    constrained = 0
    for e, (u, v) in enumerate(E):
        outer = (adj[u] | adj[v]) - {u, v}
        if len(outer) < 6:
            continue
        constrained += 1
        for c in range(k):
            s.add_clause([-x(e, c)] + [miss(w, c) for w in outer])
    # symmetry: the edges at the first vertex get colours 0, 1, ...
    for r, e in enumerate(at[verts[0]]):
        s.add_clause([x(e, r)])
    if budget:
        s.conf_budget(budget); res = s.solve_limited()
    else:
        res = s.solve()
    model = s.get_model() if res else None
    s.delete()
    if res:
        col = [next(c for c in range(k) if model[x(e, c) - 1] > 0) for e in range(m)]
        assert check(E, adj, col), "decoded colouring violates property P"
    return res, constrained


def check(E, adj, col):
    """Independent check of a decoded colouring: proper, and property P holds."""
    cover = {}
    for (u, v), c in zip(E, col):
        for w in (u, v):
            if (w, c) in cover:
                return False
            cover[(w, c)] = True
    for (u, v), c in zip(E, col):
        outer = (adj[u] | adj[v]) - {u, v}
        if sum(1 for w in outer if (w, c) in cover) > 5:
            return False
    return True


def job(args):
    n, idx, edges = args
    t0 = time.time()
    r, _ = property_p(edges, budget=500000)
    return n, idx, r, time.time() - t0


def small(N):
    t0 = time.time()
    tasks = [(n, i, g) for n in range(5, N + 1) for i, g in enumerate(load(n))]
    stats, bad, slow = {}, [], 0.0
    with mp.Pool() as pool:
        for n, idx, r, dt in pool.imap_unordered(job, tasks, chunksize=8):
            st = stats.setdefault(n, {"graphs": 0, "P": 0, "not_P": 0, "unknown": 0})
            st["graphs"] += 1
            st["P" if r else ("not_P" if r is False else "unknown")] += 1
            if not r:
                bad.append((n, idx, r))
            slow = max(slow, dt)
    for n in sorted(stats):
        print(n, stats[n], flush=True)
    print("graphs without a property-P colouring (n, index, result):", bad[:50], f"({len(bad)} total)")
    print(f"slowest instance {slow:.2f}s  [{time.time() - t0:.0f}s]")


def girth_job(args):
    import networkx as nx
    n, i, g = args
    return n, i, nx.girth(nx.Graph(g)), property_p(g, budget=500000)[0]


def girth_mode(N):
    """Failures of property P on the small graphs, broken down by (n, girth)."""
    import collections
    tasks = [(n, i, g) for n in range(5, N + 1) for i, g in enumerate(load(n))]
    fail, allg = collections.Counter(), collections.Counter()
    with mp.Pool() as pool:
        for n, i, gi, r in pool.imap_unordered(girth_job, tasks, chunksize=16):
            allg[gi] += 1
            if not r:
                fail[(n, gi)] += 1
    print("all graphs by girth:", dict(sorted(allg.items())))
    print("graphs failing property P, by (n, girth):", dict(sorted(fail.items())))


def random_mode(n, g, seeds):
    sys.path.insert(0, ".")
    from exp18_large_girth import random_graph, girth
    for seed in range(seeds):
        adj = random_graph(n, g, seed)
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        t0 = time.time()
        r, constrained = property_p(edges, budget=5_000_000)
        print({"seed": seed, "n": n, "m": len(edges), "girth": girth(adj), "odd degree": sum(len(a) % 2 for a in adj),
               "edges with 6 outer neighbours": constrained, "property P": r,
               "seconds": round(time.time() - t0, 1)}, flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "small":
        small(int(sys.argv[2]))
    elif sys.argv[1] == "girth":
        girth_mode(int(sys.argv[2]))
    else:
        random_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
