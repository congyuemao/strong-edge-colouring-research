"""M1: after the p=1 nibble with T rounds, how often can a stuck uncoloured edge e (no colour left)
be repaired by recolouring ONE coloured neighbour f whose colour is unique around e to a colour
free at f?  Reports P(stuck) and P(stuck and not one-step repairable)."""
import sys
import time

import numpy as np

from exp16_nibble import conflicts, graph, nibble

n, g, T, runs = (int(v) for v in sys.argv[1:5])
k = 20
G = graph(n, g)
E, NB = conflicts(G)
m = len(E)
t0 = time.time()
stuck = rep_fail = 0
free_counts = []
for r in range(runs):
    rs = np.random.default_rng(7919 * r + 13)
    col, avail, unc, L, U = nibble(NB, k, T, 1.0, rs)
    for e in np.nonzero(unc & (L == 0))[0]:
        stuck += 1
        nc = col[NB[e]]
        vals, cnt = np.unique(nc[nc >= 0], return_counts=True)
        unique = set(vals[cnt == 1].tolist())
        best = 0
        for f, c in zip(NB[e], nc):
            if c in unique:
                used = set(col[NB[f]][col[NB[f]] >= 0].tolist())
                free = k - len(used | {int(c)})
                best = max(best, free)
        free_counts.append(best)
        if best == 0:
            rep_fail += 1
tot = m * runs
print(f"T={T}: P(stuck)={stuck/tot:.2e} ({stuck})  P(stuck & not 1-step repairable)={rep_fail/tot:.2e} ({rep_fail})"
      f"  max free colours at a candidate f: {np.bincount(free_counts).tolist() if free_counts else []}"
      f"  [{time.time()-t0:.0f}s]")
