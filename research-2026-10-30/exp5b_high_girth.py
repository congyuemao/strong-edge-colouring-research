"""Experiment 5b: bootstrap barrier on a genuinely high-girth 4-regular graph."""
import random
import sys

import networkx as nx

from exp4_local_search import conflict_adj
from exp5_bootstrap import ball_edges, bootstrap


def short_cycle_edge(G, u, v, g):
    """True if edge uv lies on a cycle of length < g."""
    G.remove_edge(u, v)
    try:
        d = nx.single_source_shortest_path_length(G, u, cutoff=g - 2)
        return v in d
    finally:
        G.add_edge(u, v)


def raise_girth(G, g, rng, rounds=60):
    for _ in range(rounds):
        bad = [e for e in G.edges() if short_cycle_edge(G, *e, g)]
        if not bad:
            return True
        rng.shuffle(bad)
        E = list(G.edges())
        for (a, b) in bad:
            if not G.has_edge(a, b) or not short_cycle_edge(G, a, b, g):
                continue
            for _ in range(50):
                c, d = rng.choice(E)
                if not G.has_edge(c, d) or len({a, b, c, d}) < 4 or G.has_edge(a, c) or G.has_edge(b, d):
                    continue
                G.remove_edges_from([(a, b), (c, d)])
                G.add_edges_from([(a, c), (b, d)])
                if short_cycle_edge(G, a, c, g) or short_cycle_edge(G, b, d, g):
                    G.remove_edges_from([(a, c), (b, d)])
                    G.add_edges_from([(a, b), (c, d)])
                    continue
                break
            E = list(G.edges())
    return not any(short_cycle_edge(G, *e, g) for e in G.edges())


if __name__ == "__main__":
    rng = random.Random(9)
    n, g = int(sys.argv[1]), int(sys.argv[2])
    G = nx.random_regular_graph(4, n, seed=1)
    ok = raise_girth(G, g, rng)
    print(f"n={n} target girth {g}: reached={ok}, girth={nx.girth(G)}, connected={nx.is_connected(G)}")
    E, adj = conflict_adj(G)
    x = rng.choice(list(G))
    for rad in range(1, g // 2 + 2):
        seed = ball_edges(G, E, x, rad)
        row = [f"r={r}: {bootstrap(adj, seed, r):6d}" for r in (4, 5)]
        print(f"  seed = edges of ball radius {rad} ({len(seed):5d})  ->  " + "   ".join(row) + f"   (total {len(E)})", flush=True)
