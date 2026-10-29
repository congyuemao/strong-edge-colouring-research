"""Experiment 10e: the 9-pair version of Q on annealed locally dense 4-regular graphs (see exp10c)."""
import random
import sys
import time
from collections import Counter

import networkx as nx

from exp10c_dense import anneal
from exp10d_slack import solve_Q_budget

if __name__ == "__main__":
    n, runs, steps, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    c = Counter()
    t0 = time.time()
    for r in range(runs):
        for score, G in anneal(n, steps, rng):
            res = solve_Q_budget(G, 9, 20)
            c[res] += 1
            if res is not True:
                print(f"n={n}: Q9 {res}  L2-triangles={score} edges={sorted(G.edges())}", flush=True)
    print(f"n={n}: Q with 9 pairs on {sum(c.values())} dense graphs: {dict(c)}  [{time.time()-t0:.0f}s]", flush=True)
