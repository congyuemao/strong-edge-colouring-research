"""M1: after the p=1 nibble with T rounds, split the uncoloured edges into components of their conflict
graph and decide list-colourability of every component exactly (SAT).  Reports the component-size
distribution and P(edge lies in a non-colourable component)."""
import collections
import sys
import time

import numpy as np
from pysat.solvers import Minisat22

from exp16_nibble import conflicts, graph, nibble


def colourable(comp, NB, avail, inR):
    idx = {e: i for i, e in enumerate(comp)}
    k = avail.shape[1]
    s = Minisat22()
    v = lambda i, c: i * k + c + 1
    for e in comp:
        lits = [v(idx[e], c) for c in range(k) if avail[e, c]]
        if not lits:
            s.delete()
            return False
        s.add_clause(lits)
        for f in NB[e]:
            f = int(f)
            if inR[f] and idx.get(f, -1) > idx[e]:
                for c in range(k):
                    if avail[e, c] and avail[f, c]:
                        s.add_clause([-v(idx[e], c), -v(idx[f], c)])
    ok = s.solve()
    s.delete()
    return ok


n, g, T, runs = (int(x) for x in sys.argv[1:5])
G = graph(n, g)
E, NB = conflicts(G)
m = len(E)
t0 = time.time()
sizes = collections.Counter()
bad_edges = 0
for r in range(runs):
    rs = np.random.default_rng(104729 * r + 1)
    col, avail, unc, L, U = nibble(NB, 20, T, 1.0, rs)
    seen = np.zeros(m, dtype=bool)
    for s0 in np.nonzero(unc)[0]:
        if seen[s0]:
            continue
        comp, stack = [], [int(s0)]
        seen[s0] = True
        while stack:
            e = stack.pop()
            comp.append(e)
            for f in NB[e]:
                if unc[f] and not seen[f]:
                    seen[f] = True
                    stack.append(int(f))
        sizes[min(len(comp), 50)] += 1
        if not colourable(comp, NB, avail, unc):
            bad_edges += len(comp)
tot = m * runs
print(f"T={T}: P(edge in non-colourable leftover component)={bad_edges/tot:.2e} ({bad_edges} edges)  "
      f"component sizes (50 = 50+): {dict(sorted(sizes.items()))}  [{time.time()-t0:.0f}s]")
