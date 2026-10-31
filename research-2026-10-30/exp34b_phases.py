"""exp34b: exp34 with solver phases taken from an adversary state.  The adversary (exp33c's anneal2) first
minimises the trivially separable pairs, i.e. it tries to saturate every singleton conflict of e; its best state is
handed to the SAT solver as the preferred polarity of every colour variable.

Usage: exp34b_phases.py n girth seed edge anneal_steps
"""
import random
import sys
import time

import networkx as nx

from exp33_kempe import K
from exp33b_adversary import colour_all_but
from exp33c_saturation import anneal2
from exp34_sat_kil import KilSat, report_result
from graphs_hg import random_girth

n, g, seed, e, steps = map(int, sys.argv[1:6])
t0 = time.time()
G = random_girth(n, g, seed)
edges = [tuple(x) for x in G.edges()]
ks = KilSat(edges, e)
col = colour_all_but(ks.adj, e, random.Random(seed))
best = anneal2(ks.adj, col, e, steps, random.Random(seed + 1))
print(f"random n={n} girth={nx.girth(G)} seed={seed} edge {e}: adversary best (trivial, non-trivial) = {best[1]}  "
      f"[{time.time() - t0:.0f}s]", flush=True)
phases = []
for h in range(len(edges)):
    if h != e:
        phases += [ks.x(h, c) if col[h] == c else -ks.x(h, c) for c in range(K)]
ks.s.set_phases(phases)
report_result(ks, f"random n={n} girth={nx.girth(G)} seed={seed}", e, t0)
