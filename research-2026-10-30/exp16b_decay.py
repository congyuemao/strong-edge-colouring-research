"""M1: decay of the failure probability q(T) of the p=1 nibble with T rounds (20 colours), and of
P(uncoloured after T rounds).  Large samples on one large-girth graph."""
import sys
import time

import numpy as np

from exp16_nibble import conflicts, graph, nibble

n, g, runs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
k = int(sys.argv[4]) if len(sys.argv) > 4 else 20
G = graph(n, g)
E, NB = conflicts(G)
m = len(E)
rng = np.random.default_rng(7)
t0 = time.time()
Ts = list(range(3, 11))
fails = {T: 0 for T in Ts}
uncs = {T: 0 for T in Ts}
neg = {T: 0 for T in Ts}
for r in range(runs):
    # one run of 10 rounds, inspected after each round count T (same randomness, nested)
    for T in Ts:
        pass
    col = None
    for T in Ts:
        rs = np.random.default_rng(1000003 * r + 7)
        col, avail, unc, L, U = nibble(NB, k, T, 1.0, rs)
        fails[T] += int((unc & (L <= U)).sum())
        neg[T] += int((unc & (L < U)).sum())
        uncs[T] += int(unc.sum())
tot = m * runs
for T in Ts:
    print(f"k={k} T={T}: P(uncoloured)={uncs[T]/tot:.3e}  q=P(slack<=0)={fails[T]/tot:.3e} ({fails[T]})"
          f"  P(slack<0)={neg[T]/tot:.3e}  samples={tot:.1e}", flush=True)
print(f"[{time.time()-t0:.0f}s, n={n}, m={m}]")
