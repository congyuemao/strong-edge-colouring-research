"""exp32: does the local fractional Reed bound already give chi_f(L^2(G)) <= 20 for Delta = 4?

Local occupancy for the hard-core model (Davies-Kang-Pirot-Sereni) with vertex-dependent constants, at fugacity
lambda -> infinity, gives McDiarmid's local fractional Reed bound
    chi_f(H) <= max_v (d(v) + 1 + omega(v)) / 2,      omega(v) = largest clique of H containing v.
For H = L^2(G) this reads chi_f <= max_e (d(e) + 1 + omega(e)) / 2, so the fractional Erdos-Nesetril bound 20
for Delta = 4 would follow from the purely local inequality d(e) + omega(e) <= 39 for every edge e.
C5[2] has d = 19, omega = 20 (tight).  This script measures d(e) + omega(e) on all connected quartic graphs.

Usage: exp32_frac_reed.py n1,n2,...
"""
import sys
import time
from collections import Counter

import networkx as nx


def load(n):
    with open(f"graphs_n{n}.txt") as f:
        for line in f:
            yield [tuple(map(int, t.split("-"))) for t in line.split()]


def square_line_graph(edges):
    m = len(edges)
    inc = {}
    for i, (a, b) in enumerate(edges):
        inc.setdefault(a, set()).add(i)
        inc.setdefault(b, set()).add(i)
    H = nx.Graph()
    H.add_nodes_from(range(m))
    for i, (a, b) in enumerate(edges):
        near = inc[a] | inc[b]                      # edges sharing an endpoint with e_i
        far = set()
        for j in near:
            c, d = edges[j]
            far |= inc[c] | inc[d]                  # edges joined to e_i by an edge
        for j in far:
            if j > i:
                H.add_edge(i, j)
    return H


def scan(n):
    t0 = time.time()
    worst, pairs, count = None, Counter(), 0
    for gi, edges in enumerate(load(n)):
        H = square_line_graph(edges)
        om = {v: 1 for v in H}
        for C in nx.find_cliques(H):
            k = len(C)
            for v in C:
                if k > om[v]:
                    om[v] = k
        for v in H:
            d = H.degree(v)
            pairs[(d, om[v])] += 1
            s = d + om[v]
            if worst is None or s > worst[0]:
                worst = (s, gi, v, d, om[v])
        count += 1
    top = sorted(pairs, key=lambda p: -(p[0] + p[1]))[:6]
    print(f"n={n}: {count} graphs; max d+omega = {worst[0]} (graph #{worst[1]}, edge {worst[2]}: d={worst[3]}, "
          f"omega={worst[4]}) -> local fractional Reed bound {(worst[0] + 1) / 2}; "
          f"top (d, omega) pairs: {[(p, pairs[p]) for p in top]}  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    for n in map(int, sys.argv[1].split(",")):
        scan(n)
