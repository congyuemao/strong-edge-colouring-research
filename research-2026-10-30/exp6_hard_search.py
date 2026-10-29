"""Experiment 6: hill-climb over 4-regular graphs (double-edge switches) to maximise the strong
chromatic index, excluding graphs that contain C5[2] as a component.  Then test property Q and
the 'some 2-factorization is 10+10' property on the hardest graphs found."""
import json
import random
import sys
import time

import networkx as nx

from exp3_pairs import solve_Q
from sec import balanced_strong_colouring, chromatic, conflict_graph, norm


def chi_s(G):
    return chromatic(conflict_graph(G, [norm(e) for e in G.edges()]))


def density(G):
    return conflict_graph(G, [norm(e) for e in G.edges()]).number_of_edges()


def switch(G, rng):
    E = list(G.edges())
    for _ in range(100):
        (a, b), (c, d) = rng.sample(E, 2)
        if rng.random() < 0.5:
            c, d = d, c
        if len({a, b, c, d}) < 4 or G.has_edge(a, c) or G.has_edge(b, d):
            continue
        H = G.copy()
        H.remove_edges_from([(a, b), (c, d)])
        H.add_edges_from([(a, c), (b, d)])
        if nx.is_connected(H):
            return H
    return None


def climb(n, rng, steps):
    G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
    while not nx.is_connected(G):
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
    score = (chi_s(G), density(G))
    for _ in range(steps):
        H = switch(G, rng)
        if H is None:
            continue
        s = (chi_s(H), density(H))
        if s >= score:
            G, score = H, s
    return G, score


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 1200
    t0 = time.time()
    best = {}
    while time.time() - t0 < budget:
        n = rng.choice(range(11, 23))
        G, (c, dens) = climb(n, rng, steps=150)
        if n not in best or (c, dens) > best[n][0]:
            best[n] = ((c, dens), sorted(map(list, G.edges())))
            Q = solve_Q(G)
            bal = balanced_strong_colouring(G) is not None
            print(f"n={n:2d} chi_s={c:2d} |E(L2)|={dens:4d} Q={Q} 10+10 2-factorization={bal}  [{time.time()-t0:.0f}s]", flush=True)
    json.dump({n: v for n, v in best.items()}, open("exp6_best.json", "w"))
