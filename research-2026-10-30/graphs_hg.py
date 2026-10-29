"""Structured 4-regular graphs of girth >= 5 for route-Q tests."""
import itertools
import random

import networkx as nx

from exp5b_high_girth import raise_girth


def _proj_points(dim, q=3):
    pts = []
    for v in itertools.product(range(q), repeat=dim):
        if any(v):
            first = next(x for x in v if x)
            if first == 1:
                pts.append(v)
    return pts


def pg23_incidence():
    """Incidence graph of PG(2,3): the (4,6)-cage, 26 vertices."""
    P = _proj_points(3)
    G = nx.Graph()
    for p in P:
        for l in P:
            if sum(a * b for a, b in zip(p, l)) % 3 == 0:
                G.add_edge(("p", p), ("l", l))
    return nx.convert_node_labels_to_integers(G)


def gq33_incidence():
    """Incidence graph of the symplectic quadrangle W(3): the (4,8)-cage, 80 vertices."""
    P = _proj_points(4)
    form = lambda x, y: (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % 3
    lines = set()
    for a, b in itertools.combinations(P, 2):
        if form(a, b) == 0:
            span = set()
            for s, t in itertools.product(range(3), repeat=2):
                v = tuple((s * x + t * y) % 3 for x, y in zip(a, b))
                if any(v):
                    f = next(x for x in v if x)
                    inv = 1 if f == 1 else 2
                    span.add(tuple((inv * x) % 3 for x in v))
            lines.add(frozenset(span))
    G = nx.Graph()
    for i, L in enumerate(lines):
        for p in L:
            G.add_edge(("p", p), ("l", i))
    return nx.convert_node_labels_to_integers(G)


def random_girth(n, g, seed):
    rng = random.Random(seed)
    G = nx.random_regular_graph(4, n, seed=seed)
    ok = raise_girth(G, g, rng, rounds=200)
    return G if ok and nx.is_connected(G) else None


if __name__ == "__main__":
    for name, G in [("PG(2,3)", pg23_incidence()), ("W(3)", gq33_incidence())]:
        print(name, G.number_of_nodes(), set(dict(G.degree()).values()), nx.girth(G))
    for n, g in [(30, 5), (60, 6), (200, 7)]:
        G = random_girth(n, g, 1)
        print(n, g, None if G is None else nx.girth(G))
