"""exp35: two-stage adversary for the Kempe insertion lemma in the "danger zone" (girth 4-6, n = 30-200).

Stage 1 (fast): make e blocked and every singleton conflict of e saturated (it sees all 19 other colours), i.e.
no single recolouring of a conflict frees a colour.  Energy = 1000 * (#colours missing on N(e)) + #(singleton f,
colour b) with b missing at f.  Only conflicts of e and their neighbourhoods are evaluated, so steps are cheap.
Stage 2 (only if stage 1 reaches 0): keep saturation and minimise the number of separable pairs (Kempe chains).
Energy = 1000 * stage-1 energy + #separable pairs.  Reaching 0 is a counterexample to one-pair insertion; it is then
tested at depth 2 and by BFS over swap sequences.

Usage: exp35_saturate.py n girth seeds edges_per_graph steps1 steps2
"""
import math
import random
import sys
import time
from collections import Counter

import networkx as nx

from exp33_kempe import K, l2_adj, swap, component, depth_two
from exp33b_adversary import colour_all_but, free, n_separable, deep_search
from graphs_hg import random_girth


def sat_energy(adj, col, e):
    cnt = Counter(col[f] for f in adj[e])
    miss = K - len(cnt)
    if miss:
        return 1000 * miss
    tot = 0
    for f in adj[e]:
        if cnt[col[f]] == 1:
            seen = {col[g] for g in adj[f]}
            tot += sum(1 for b in range(K) if b != col[f] and b not in seen)
    return tot


def anneal(adj, col, e, steps, rng, energy, region, T0):
    E = energy()
    best = E
    for t in range(steps):
        T = T0 * (1 - t / steps) + 0.05
        f = rng.choice(region)
        old = list(col)
        if rng.random() < 0.5:
            fr = [c for c in free(adj, col, f) if c != col[f]]
            if not fr:
                continue
            col[f] = rng.choice(fr)
        else:
            c = rng.randrange(K)
            if c == col[f]:
                continue
            swap(col, component(adj, col, f, col[f], c), col[f], c)
        E2 = energy()
        if E2 <= E or rng.random() < math.exp((E - E2) / T):
            E = E2
            if E < best:
                best = E
            if E == 0:
                return 0
        else:
            col[:] = old
    return best


def main():
    n, g, nseeds, nedges, s1, s2 = map(int, sys.argv[1:7])
    t0 = time.time()
    for seed in range(nseeds):
        G = random_girth(n, g, seed) if g > 3 else nx.random_regular_graph(4, n, seed=seed)
        if G is None:
            continue
        edges = [tuple(x) for x in G.edges()]
        adj = l2_adj(edges)
        rng = random.Random(seed)
        for e in rng.sample(range(len(edges)), nedges):
            if len(adj[e]) < K:
                continue
            region = set(adj[e])
            for f in list(region):
                region.update(adj[f])
            region.discard(e)
            region = sorted(region)
            col = colour_all_but(adj, e, rng)
            b1 = anneal(adj, col, e, s1, rng, lambda: sat_energy(adj, col, e), region, 3.0)
            msg = f"n={n} girth={nx.girth(G)} seed={seed} edge {e}: stage 1 min = {b1}"
            if b1 == 0:
                b2 = anneal(adj, col, e, s2, rng,
                            lambda: 1000 * sat_energy(adj, col, e) + (n_separable(adj, col, e)
                                                                       if sat_energy(adj, col, e) == 0 else 190),
                            region, 2.0)
                msg += f"; SATURATED; stage 2 min #separable (all non-trivial) = {b2}"
                if b2 == 0:
                    d2 = depth_two(adj, col, e)
                    msg += "; STUCK at depth 1; depth 2: " + ("repaired" if d2 else
                                                              f"fails; BFS<=3: {deep_search(adj, col, e, 3)}")
                    msg += f"\n    colouring: {col}"
            print(msg + f"  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
