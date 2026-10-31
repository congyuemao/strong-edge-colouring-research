"""exp33e: the adversary runs of exp33b, one mode per log.

  long13  : two hardest n = 13 edges, 30000 steps, 3 seeds                       -> exp33b_long.log
  dense   : random 4-regular graphs n = 24..200, densest edges, radius 3         -> exp33b_dense.log
  strong  : girth 5, 6, 7 graphs, 5000 vs 60000 steps, radius 3                 -> exp33b_strong.log
  trend   : one girth-5 edge, 12 rounds of 40000 steps from the current state    -> exp33b_trend.log
  g88048  : n = 14 #88048 (the graph where local occupancy gives 21)             -> exp33b_88048.log

Usage: exp33e_drivers.py mode
"""
import random
import sys
import time

import networkx as nx

from exp33_kempe import l2_adj, load, depth_two
from exp33b_adversary import colour_all_but, anneal, n_separable
from graphs_hg import random_girth


def long13(t0):
    g13 = list(load(13))
    for gi, e in ((10760, 19), (9684, 21)):
        adj = l2_adj(g13[gi])
        for s in range(3):
            rng = random.Random(s)
            col = colour_all_but(adj, e, rng)
            best, _ = anneal(adj, col, e, 30000, rng)
            print(f"n=13 #{gi} edge {e} seed {s}: 30000 steps -> min #separable = {best}  [{time.time() - t0:.0f}s]",
                  flush=True)


def dense(t0):
    for n in (24, 40, 80, 200):
        for s in range(3):
            G = nx.random_regular_graph(4, n, seed=100 + s)
            adj = l2_adj([tuple(x) for x in G.edges()])
            rng = random.Random(s)
            dens = sorted((-sum(1 for f in adj[e] for g in adj[f] if g in set(adj[e])), e)
                          for e in range(len(adj)) if len(adj[e]) >= 20)
            for _, e in dens[:2]:
                col = colour_all_but(adj, e, rng)
                best, _ = anneal(adj, col, e, 15000, rng, radius=3)
                tri = sum(nx.triangles(G).values()) // 3
                print(f"random n={n} seed={s} (triangles {tri}) edge {e} d={len(adj[e])}: min #separable = {best}  "
                      f"[{time.time() - t0:.0f}s]", flush=True)


def strong(t0):
    for n, g, s in ((60, 5, 0), (200, 6, 1), (500, 7, 0)):
        G = random_girth(n, g, s)
        adj = l2_adj([tuple(x) for x in G.edges()])
        rng = random.Random(11)
        for e in rng.sample(range(len(adj)), 2):
            col = colour_all_but(adj, e, rng)
            res = [(st, anneal(adj, list(col), e, st, random.Random(st), radius=3)[0]) for st in (5000, 60000)]
            print(f"n={n} girth={nx.girth(G)} edge {e}: min #separable by steps {res}  [{time.time() - t0:.0f}s]",
                  flush=True)


def trend(t0):
    G = random_girth(60, 5, 0)
    adj = l2_adj([tuple(x) for x in G.edges()])
    e = 57
    col = colour_all_but(adj, e, random.Random(5))
    total = 0
    for rnd in range(12):
        best, _ = anneal(adj, col, e, 40000, random.Random(rnd), radius=3)
        total += 40000
        cur = n_separable(adj, col, e) if len({col[f] for f in adj[e]}) == 20 else None
        print(f"after {total} steps: min this round {best}, current {cur}  [{time.time() - t0:.0f}s]", flush=True)
        if best == 0:
            print("depth-2 repair:", depth_two(adj, col, e) is not None, flush=True)
            break


def g88048(t0):
    edges = next(ed for i, ed in enumerate(load(14)) if i == 88048)
    adj = l2_adj(edges)
    for e in (15,) + tuple(f for f in range(len(adj)) if f != 15 and len(adj[f]) >= 21)[:3]:
        for s in range(4):
            rng = random.Random(s)
            col = colour_all_but(adj, e, rng)
            best, _ = anneal(adj, col, e, 40000, rng, radius=3)
            print(f"n=14 #88048 edge {e} {edges[e]} d={len(adj[e])} seed {s}: min #separable = {best}  "
                  f"[{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    {"long13": long13, "dense": dense, "strong": strong, "trend": trend, "g88048": g88048}[sys.argv[1]](time.time())
