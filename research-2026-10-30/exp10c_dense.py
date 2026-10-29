"""Experiment 10c: look for property-Q counterexamples among locally dense 4-regular graphs.

Exhaustive lists stop at n = 13, and below n = 11 Q is trivial (at most 20 edges).  The dangerous
graphs are larger ones that are locally almost as dense as C5[2] (the extremal graph, L^2 = K20).
  (a) rings of near-extremal blocks: k copies of C5[2], K5 or K4,4, each with one edge removed,
      reconnected in a ring;
  (b) annealing over 4-regular graphs on n vertices by double-edge switches, maximizing the number
      of triangles of L^2 (local density of the conflict graph); Q is tested on the densest graphs
      met along the way."""
import itertools
import math
import random
import sys
import time

import networkx as nx

from exp3_pairs import solve_Q
from sec import blowup_cycle, norm


def l2_adj(G):
    E = [norm(e) for e in G.edges()]
    inc = {v: [e for e in E if v in e] for v in G}
    adj = {e: set() for e in E}
    for e in E:
        near = set(e) | set(G[e[0]]) | set(G[e[1]])
        for w in near:
            for f in inc[w]:
                if f != e:
                    adj[e].add(f)
    return adj


def l2_triangles(G):
    adj = l2_adj(G)
    return sum(len(adj[e] & adj[f]) for e in adj for f in adj[e]) // 6


def ring(block, k):
    """k copies of `block`, one edge (u,v) removed from each, joined v_i - u_{i+1}."""
    u, v = next(iter(block.edges()))
    G = nx.Graph()
    for i in range(k):
        B = nx.relabel_nodes(block, {x: (i, x) for x in block})
        B.remove_edge((i, u), (i, v))
        G.update(B)
    for i in range(k):
        G.add_edge((i, v), ((i + 1) % k, u))
    return nx.convert_node_labels_to_integers(G)


def anneal(n, steps, rng):
    G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
    while not nx.is_connected(G):
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
    score = l2_triangles(G)
    best = [(score, G.copy())]
    T = 5.0
    for step in range(steps):
        E = list(G.edges())
        (a, b), (c, d) = rng.sample(E, 2)
        if len({a, b, c, d}) < 4:
            continue
        if rng.random() < 0.5:
            c, d = d, c
        if G.has_edge(a, c) or G.has_edge(b, d):
            continue
        G.remove_edges_from([(a, b), (c, d)])
        G.add_edges_from([(a, c), (b, d)])
        if not nx.is_connected(G):
            G.remove_edges_from([(a, c), (b, d)])
            G.add_edges_from([(a, b), (c, d)])
            continue
        new = l2_triangles(G)
        if new >= score or rng.random() < math.exp((new - score) / T):
            score = new
            if score > best[-1][0]:
                best.append((score, G.copy()))
        else:
            G.remove_edges_from([(a, c), (b, d)])
            G.add_edges_from([(a, b), (c, d)])
        T = max(0.05, T * 0.999)
    return best[-6:]


if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time()
    if mode == "rings":
        blocks = [("C5[2]", blowup_cycle(5)), ("K5", nx.complete_graph(5)),
                  ("K4,4", nx.complete_bipartite_graph(4, 4)), ("C6[2]", blowup_cycle(6)),
                  ("C7(1,2)", nx.circulant_graph(7, [1, 2])), ("K6-M", nx.complement(nx.Graph([(0, 1), (2, 3), (4, 5)])))]
        for (name, B), k in itertools.product(blocks, (2, 3, 4)):
            G = ring(B, k)
            assert all(d == 4 for _, d in G.degree())
            t = time.time()
            ok = solve_Q(G)
            print(f"ring {name} x{k}: n={G.number_of_nodes()} m={G.number_of_edges()} Q={'yes' if ok else 'NO'} [{time.time()-t:.1f}s]", flush=True)
    else:
        n, runs, steps, seed = map(int, sys.argv[2:6])
        rng = random.Random(seed)
        bad = 0
        tested = 0
        for r in range(runs):
            for score, G in anneal(n, steps, rng):
                t = time.time()
                ok = solve_Q(G)
                tested += 1
                if not ok:
                    bad += 1
                    print(f"n={n} run {r}: Q FAILS  L2-triangles={score} edges={sorted(G.edges())}", flush=True)
            print(f"n={n} run {r}: best L2-triangles={score} girth={nx.girth(G)} last Q={'yes' if ok else 'NO'} [{time.time()-t:.1f}s]", flush=True)
        print(f"n={n}: tested {tested} dense graphs, Q fails on {bad}  [{time.time()-t0:.0f}s]", flush=True)
