"""exp19b: property M on structured dense quartic graphs beyond n = 13.

Families: doubled cycles C_k[2] and circulants C_n(a, b).  For each graph: chi' (4 or 5),
property M_t at budget 20 by SAT (t = chi'), and for class-1 graphs on an even number of vertices
the exact least budget over all 1-factorisations (exp19_property_m.exact_min_budget).
"""
import sys
import time

import networkx as nx

from exp19_property_m import edge_colourable, exact_min_budget, property_m, strong_colourable, structure


def doubled_cycle(k):
    G = nx.Graph([((i, s), ((i + 1) % k, t)) for i in range(k) for s in range(2) for t in range(2)])
    return nx.convert_node_labels_to_integers(G)


def circulant(n, a, b):
    return nx.circulant_graph(n, [a, b])


def report(name, G, exact=True):
    t0 = time.time()
    edges = list(G.edges())
    c1 = edge_colourable(edges, 4)[0]
    t = 4 if c1 else 5
    m20 = property_m(edges, t, 20, budget=2_000_000)
    ex = exact_min_budget(edges)[0] if (exact and c1 and G.number_of_nodes() % 2 == 0) else None
    E, adj, share, conf = structure(edges)
    L = nx.Graph(); L.add_nodes_from(range(len(E))); L.add_edges_from(conf)
    w = max(len(c) for c in nx.find_cliques(L))   # lower bound for chi'_s
    ub = 20                                       # upper bound: descend while SAT is found quickly
    while ub > w and strong_colourable(edges, ub - 1, budget=200_000):
        ub -= 1
    print(f"{name:12s} n={G.number_of_nodes():2d} girth={nx.girth(G)} class={1 if c1 else 2} "
          f"chi'_s in [{w},{ub}]  M{t}@20={m20}  exact M4 budget={ex}  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    for k in range(5, 11):
        report(f"C{k}[2]", doubled_cycle(k), exact=k <= 8)
    for n in range(9, 21):
        for a, b in ((1, 2), (1, 3)):
            if 2 * b < n and nx.is_connected(circulant(n, a, b)):
                report(f"C{n}({a},{b})", circulant(n, a, b), exact=n <= 16)
