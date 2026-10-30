"""exp20: hill-climbing search for quartic graphs that break property M (n >= 14).

For a class-1 graph on an even number of vertices every class of a 4-edge-colouring is a perfect
matching, so the least budget of the 4-matching form is
  B*(G) = min over 1-factorisations {M_1..M_4} of  sum_i chi(H(M_i)),
computed exactly by enumerating perfect matchings.  B*(G) >= 21 breaks the 4-matching form; it
breaks property M itself only if the 5-matching form also fails, which is then checked by SAT.

Search: random double-edge switches (keeping the graph simple, connected and 4-regular), score
(B*, mean chi(H(P)) over all perfect matchings P), accepting moves that do not lower the score and,
with small probability, moves that do.  A switch that makes the graph class 2 is checked for the
5-matching form at budget 20 and otherwise rejected.

Usage: exp20_search.py n1,n2,.. workers_per_n seconds [mean|k6] [seed graph n:index]
  mode k6 scores (B*, share of perfect matchings with chi >= 6, mean chi); a seed graph from
  graphs_n*.txt is grown to n vertices by vertex insertion before the climb.
"""
import multiprocessing as mp
import random
import sys
import time

import networkx as nx

from exp19_property_m import property_m


def chromatic(nb):
    """Exact chromatic number of a small graph (adjacency sets) by backtracking."""
    n = len(nb)
    order = sorted(range(n), key=lambda v: -len(nb[v]))
    best = [n]

    def rec(i, col, k):
        if k >= best[0]:
            return
        if i == n:
            best[0] = k; return
        v = order[i]
        used = {col[u] for u in nb[v] if u in col}
        for c in range(k):
            if c not in used:
                col[v] = c; rec(i + 1, col, k); del col[v]
        col[v] = k; rec(i + 1, col, k + 1); del col[v]

    rec(0, {}, 0)
    return best[0]


def analyse(G):
    """Return (B*, mean chi over perfect matchings, #perfect matchings, share of perfect matchings
    with chi >= 6), or None if there is no 1-factorisation."""
    nodes = sorted(G); idx = {v: i for i, v in enumerate(nodes)}; n = len(nodes)
    E = sorted((min(idx[u], idx[v]), max(idx[u], idx[v])) for u, v in G.edges())
    eid = {e: i for i, e in enumerate(E)}
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    at = [[eid[(min(v, w), max(v, w))] for w in adj[v]] for v in range(n)]
    pms = []

    def rec(used, chosen):
        free = next((v for v in range(n) if not used >> v & 1), None)
        if free is None:
            pms.append(chosen); return
        for i in at[free]:
            u, v = E[i]
            if not used >> u & 1 and not used >> v & 1:
                rec(used | 1 << u | 1 << v, chosen | 1 << i)

    rec(0, 0)
    cost = {}
    for P in pms:
        M = [E[i] for i in range(len(E)) if P >> i & 1]
        owner = {}
        for j, (u, v) in enumerate(M):
            owner[u] = j; owner[v] = j
        nb = [set() for _ in M]
        for j, (u, v) in enumerate(M):
            for x in (u, v):
                for y in adj[x]:
                    if owner[y] != j:
                        nb[j].add(owner[y])
        cost[P] = chromatic(nb)
    by_edge = [[P for P in pms if P >> e & 1] for e in range(len(E))]
    full = (1 << len(E)) - 1
    best = [None]
    lo = min(cost.values()) if cost else 0

    def fac(left, total, depth):
        if best[0] is not None and total + (4 - depth) * lo >= best[0]:
            return
        if not left:
            best[0] = total; return
        e = (left & -left).bit_length() - 1
        for P in by_edge[e]:
            if P & left == P:
                fac(left & ~P, total + cost[P], depth + 1)

    fac(full, 0, 0)
    if best[0] is None:
        return None
    frac6 = sum(1 for c in cost.values() if c >= 6) / len(cost)
    return best[0], sum(cost.values()) / len(cost), len(pms), frac6


def switch(G, rng):
    H = G.copy()
    for _ in range(100):
        (a, b), (c, d) = rng.sample(list(H.edges()), 2)
        if len({a, b, c, d}) < 4:
            continue
        if rng.random() < 0.5:
            c, d = d, c
        if H.has_edge(a, c) or H.has_edge(b, d):
            continue
        H.remove_edges_from([(a, b), (c, d)]); H.add_edges_from([(a, c), (b, d)])
        if nx.is_connected(H):
            return H
        H.remove_edges_from([(a, c), (b, d)]); H.add_edges_from([(a, b), (c, d)])
    return None


def expand(G, rng):
    """Grow a quartic graph by one vertex: delete two disjoint edges ab, cd and join a new vertex
    to a, b, c, d."""
    while True:
        (a, b), (c, d) = rng.sample(list(G.edges()), 2)
        if len({a, b, c, d}) == 4:
            H = G.copy(); x = max(H) + 1
            H.remove_edges_from([(a, b), (c, d)]); H.add_edges_from([(x, a), (x, b), (x, c), (x, d)])
            return H


def score(r, mode):
    return (r[0], r[3], r[1]) if mode == "k6" else (r[0], r[1])


def worker(args):
    n, seed, seconds, mode, start = args
    rng = random.Random(seed)
    if start is not None:
        G = nx.Graph(start)
        while G.number_of_nodes() < n or analyse(G) is None:
            G = expand(G, rng) if G.number_of_nodes() < n else switch(G, rng) or G
    else:
        G = nx.random_regular_graph(4, n, seed=seed)
    while not nx.is_connected(G) or analyse(G) is None:
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10 ** 9))
    cur = analyse(G); best, bestG = cur, G
    t0 = time.time(); steps = 0; class2_checked = 0; breaks = []
    while time.time() - t0 < seconds:
        H = switch(G, rng); steps += 1
        if H is None:
            continue
        r = analyse(H)
        if r is None:
            class2_checked += 1
            if property_m(list(H.edges()), 5, 20, budget=200000) is not True:
                breaks.append(("class2 graph, M5@20 not shown", sorted(H.edges())))
            continue
        if r[0] >= 21:
            m5 = property_m(list(H.edges()), 5, 20, budget=2000000)
            breaks.append((f"B*={r[0]}, M5@20={m5}", sorted(H.edges())))
        if score(r, mode) >= score(cur, mode) or rng.random() < 0.02:
            G, cur = H, r
            if score(cur, mode) > score(best, mode):
                best, bestG = cur, G
    return n, seed, best, sorted(bestG.edges()), steps, class2_checked, breaks


if __name__ == "__main__":
    ns = [int(v) for v in sys.argv[1].split(",")]
    per, seconds = int(sys.argv[2]), int(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else "mean"      # "mean" or "k6"
    seedgraph = None
    if len(sys.argv) > 5:                                    # e.g. 12:1529 = graphs_n12.txt line 1529
        from exp19_property_m import load
        gn, gi = (int(v) for v in sys.argv[5].split(":"))
        seedgraph = list(load(gn))[gi]
    tasks = [(n, 1000 * n + s + (500 if seedgraph else 0), seconds, mode, seedgraph)
             for n in ns for s in range(per)]
    results = {}
    with mp.Pool(min(len(tasks), mp.cpu_count())) as pool:
        for n, seed, best, edges, steps, c2, breaks in pool.imap_unordered(worker, tasks):
            results.setdefault(n, []).append((best, seed, steps, c2, edges, breaks))
            print(f"n={n} seed={seed}: best B*={best[0]} mean chi={best[1]:.3f} #PM={best[2]} K6 share={best[3]:.3f} "
                  f"steps={steps} class2 seen={c2} breaks={len(breaks)}", flush=True)
            for b in breaks[:3]:
                print("   BREAK:", b[0], b[1], flush=True)
    for n in sorted(results):
        top = max(results[n], key=lambda r: score(r[0], mode))
        print(f"n={n}: highest B* = {top[0][0]} (mean chi {top[0][1]:.3f}), seed {top[1]}; edges {top[4]}")
