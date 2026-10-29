"""Experiment 5: the greedy-ordering barrier.
A greedy strong colouring with k colours along an order needs every edge (except a few final
ones) to have >= 25-k conflicting edges coloured AFTER it.  Reversing the order, this is
r-neighbour bootstrap percolation on L^2(G) with r = 25-k, from a small seed set.
HSY (21 colours) use r = 4; 20 colours needs r = 5.  We measure how far each spreads."""
import random
import sys
from collections import deque

import networkx as nx

from exp4_local_search import conflict_adj


def bootstrap(adj, seed, r):
    infected = set(seed)
    cnt = [0] * len(adj)
    q = deque(seed)
    while q:
        v = q.popleft()
        for w in adj[v]:
            if w in infected:
                continue
            cnt[w] += 1
            if cnt[w] >= r:
                infected.add(w)
                q.append(w)
    return len(infected)


def ball_edges(G, E, x, rad):
    dist = nx.single_source_shortest_path_length(G, x, cutoff=rad)
    return [i for i, (a, b) in enumerate(E) if a in dist and b in dist]


if __name__ == "__main__":
    rng = random.Random(5)
    for n in (200, 1000, 4000):
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
        E, adj = conflict_adj(G)
        x = rng.choice(list(G))
        print(f"n={n} m={len(E)} girth={nx.girth(G)}")
        for rad in (1, 2, 3, 4):
            seed = ball_edges(G, E, x, rad)
            row = [f"r={r}: {bootstrap(adj, seed, r):5d}" for r in (4, 5, 6)]
            print(f"  seed=ball radius {rad} ({len(seed):4d} edges)  ->  " + "   ".join(row), flush=True)
