"""exp32b: the best local-occupancy bound at finite fugacity for one edge-neighbourhood type of L^2(G).

Hard-core model at fugacity lam on the current graph; condition on X outside N[u], let F be the uncovered part of
N(u).  Then P(u in X | .) = lam / (lam + Z_F) and E(|X cap N(u)| | .) = S_F / (lam + Z_F), S_F = lam Z_F'(lam).
Local occupancy at u with constants (beta, gamma):  beta P + gamma E >= 1 for every F, i.e.
    (beta - 1) lam >= Z_F - gamma S_F        for every induced subgraph F of L^2[N(u)].
The greedy fractional colouring of Davies-Kang-Pirot-Sereni then finishes u by time beta + gamma deg(u), so with
vertex-dependent constants and one global lam, chi_f <= max_u min_gamma (1 + gamma deg(u) + max_F (Z_F - gamma S_F)/lam).

All 2^d subsets F are handled by the recursion Z[F] = Z[F - x] + lam Z[F - N[x]] (x the lowest vertex of F),
vectorised over the masks with a given lowest vertex.

Usage: exp32b_occupancy.py demo
"""
import sys

import networkx as nx
import numpy as np

from exp32_frac_reed import load, square_line_graph


def partition_sums(adj, lam):
    """Z[F], S[F] for all subsets F of the vertex set of adj (list of neighbour bitmasks)."""
    d = len(adj)
    Z = np.empty(1 << d)
    S = np.empty(1 << d)
    Z[0], S[0] = 1.0, 0.0
    for i in range(d - 1, -1, -1):
        k = np.arange(1 << (d - 1 - i), dtype=np.int64)
        m = (k << (i + 1)) | (1 << i)
        rest = m ^ (1 << i)
        nb = m & ~(adj[i] | (1 << i))
        Z[m] = Z[rest] + lam * Z[nb]
        S[m] = S[rest] + lam * (Z[nb] + S[nb])
    return Z, S


def best_bound(adj, lam):
    d = len(adj)
    Z, S = partition_sums(adj, lam)
    f = lambda g: 1 + g * d + float(np.max(Z - g * S)) / lam
    lo, hi = 0.0, 1.0                                # f is convex in gamma
    for _ in range(60):
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(a) <= f(b):
            hi = b
        else:
            lo = a
    g = (lo + hi) / 2
    return f(g), g


def neighbourhood(H, v):
    nbrs = sorted(H[v])
    idx = {x: i for i, x in enumerate(nbrs)}
    adj = [0] * len(nbrs)
    for x in nbrs:
        for y in H[x]:
            if y in idx:
                adj[idx[x]] |= 1 << idx[y]
    return adj


def tree_edge_type():
    """L^2-neighbourhood of an edge in a 4-regular graph of girth >= 9 (a depth-3 tree around the edge)."""
    T = nx.Graph()
    T.add_edge(0, 1)
    frontier, nxt = [0, 1], 2
    for depth in range(3):
        new = []
        for x in frontier:
            while T.degree(x) < 4:
                T.add_edge(x, nxt)
                new.append(nxt)
                nxt += 1
        frontier = new
    edges = [tuple(e) for e in T.edges()]
    H = square_line_graph(edges)
    e0 = edges.index((0, 1)) if (0, 1) in edges else edges.index((1, 0))
    return neighbourhood(H, e0)


if __name__ == "__main__":
    if sys.argv[1] == "demo":
        cases = {"tree-like (girth >= 9)": tree_edge_type()}
        g10 = list(load(10))
        H = square_line_graph(g10[58])
        cases["C5[2] (n=10 #58)"] = neighbourhood(H, 0)
        for gi, e in ((88048, 15),):
            for i, edges in enumerate(load(14)):
                if i == gi:
                    H = square_line_graph(edges)
                    cases[f"n=14 #{gi} edge {e} (d=24, omega=17)"] = neighbourhood(H, e)
                    break
        for name, adj in cases.items():
            res = [(lam,) + best_bound(adj, lam) for lam in (0.05, 0.1, 0.2, 0.5, 1, 2, 5, 20, 100)]
            best = min(res, key=lambda r: r[1])
            print(f"{name}: d = {len(adj)}; " + "; ".join(f"lam={l}: {b:.3f}" for l, b, _ in res)
                  + f"  -> best {best[1]:.3f} at lam={best[0]}, gamma={best[2]:.3f}", flush=True)
