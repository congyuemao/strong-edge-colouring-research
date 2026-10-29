"""Experiment 16 (M1): does a bounded-radius random colouring procedure leave enough room for the
Lovasz Local Lemma on large-girth 4-regular graphs?

Procedure (multi-round nibble, k colours).  Every edge keeps a list L(e) of colours not used by its
coloured conflicts.  In round t each uncoloured edge is activated with probability p, picks a
uniform colour from L(e), and keeps it unless an activated conflict picked the same colour.  After
T rounds the edge e "fails" if it is uncoloured and |L(e)| <= u(e), u(e) = #uncoloured conflicts:
if no edge fails, the remaining edges can be coloured greedily in any order.

Dependency radius (corrected after the Codex review): each round propagates dependency by TWO
conflict-graph hops -- a tentative colour depends on the edge's list (one hop: its neighbours'
earlier successes) and the clash test looks at the neighbours' tentative colours (another hop).
The state after round t depends on randomness within radius 2t-1, the lists within 2t, and the
final test |L(e)| <= u(e) within radius 2T.  Two failure events are dependent once their radius-2T
balls meet, so the LLL needs
  e * q * (D + 1) < 1,  q = P(e fails),  D = |B(4T)| = 3^(8T+1) - 2
(on the 4-regular tree |B(r)| = 3^(2r+1) - 2 exactly, so D grows by 3^8 = 6561 per round).
We measure q by simulation on a random 4-regular graph of large girth and compare.

Usage: exp16_nibble.py n girth k T p runs [schedule]"""
import os
import random
import sys
import time

import networkx as nx
import numpy as np

from exp4_local_search import conflict_adj
from exp5b_high_girth import raise_girth


def graph(n, g, seed=1):
    path = f"hg_n{n}_g{g}_s{seed}.edges"
    if os.path.exists(path):
        G = nx.read_edgelist(path, nodetype=int)
    else:
        G = nx.random_regular_graph(4, n, seed=seed)
        assert raise_girth(G, g, random.Random(seed))
        nx.write_edgelist(G, path, data=False)
    return G


def conflicts(G):
    E, adj = conflict_adj(G)
    assert all(len(a) == 24 for a in adj)
    return E, np.array(adj, dtype=np.int32)


def nibble(NB, k, T, p, rng, schedule=None):
    m = NB.shape[0]
    col = np.full(m, -1, dtype=np.int32)
    avail = np.ones((m, k), dtype=bool)
    rows = np.arange(m)
    for t in range(T):
        pt = schedule[t] if schedule is not None else p
        unc = col < 0
        act = unc & (rng.random(m) < pt) & avail.any(1)
        keys = rng.random((m, k))
        keys[~avail] = -1.0
        choice = keys.argmax(1).astype(np.int32)
        choice[~act] = -1
        nbc = choice[NB]
        clash = (nbc == choice[:, None]).any(1)
        keep = act & ~clash
        col[keep] = choice[keep]
        f = np.nonzero(keep)[0]
        if len(f):
            avail[NB[f].ravel(), np.repeat(col[f], NB.shape[1])] = False
    unc = col < 0
    L = avail.sum(1)
    U = (col[NB] < 0).sum(1)
    return col, avail, unc, L, U


def greedy_finish(NB, col, avail):
    """Colour the rest, always taking an uncoloured edge with the fewest available colours."""
    col = col.copy()
    avail = avail.copy()
    left = set(np.nonzero(col < 0)[0].tolist())
    while left:
        e = min(left, key=lambda i: avail[i].sum())
        opts = np.nonzero(avail[e])[0]
        if len(opts) == 0:
            return False, len(left)
        c = opts[0]
        col[e] = c
        avail[NB[e], c] = False
        left.discard(e)
    return True, 0


def ball_sizes(NB, src, rmax):
    seen = {src}
    frontier = [src]
    sizes = []
    for _ in range(rmax):
        nxt = []
        for v in frontier:
            for w in NB[v]:
                w = int(w)
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
        frontier = nxt
        sizes.append(len(seen))
    return sizes


if __name__ == "__main__":
    n, g, k, T = (int(v) for v in sys.argv[1:5])
    p = float(sys.argv[5])
    runs = int(sys.argv[6])
    G = graph(n, g)
    E, NB = conflicts(G)
    m = len(E)
    rng = np.random.default_rng(0)
    t0 = time.time()
    fails = 0
    unc_tot = 0
    slack_hist = {}
    finished = 0
    for r in range(runs):
        col, avail, unc, L, U = nibble(NB, k, T, p, rng)
        fail = unc & (L <= U)
        fails += int(fail.sum())
        unc_tot += int(unc.sum())
        s = (L - U)[unc]
        for v, c in zip(*np.unique(s, return_counts=True)):
            slack_hist[int(v)] = slack_hist.get(int(v), 0) + int(c)
        if r < 3:
            ok, _ = greedy_finish(NB, col, avail)
            finished += ok
    q = fails / (m * runs)
    print(f"n={n} girth={nx.girth(G)} m={m} k={k} T={T} p={p} runs={runs}: "
          f"uncoloured {unc_tot / (m * runs):.4f}  fail q={q:.2e} ({fails} events)  "
          f"greedy-finish ok {finished}/{min(runs, 3)}  [{time.time() - t0:.0f}s]", flush=True)
    lo = sorted(slack_hist)[:8]
    print("   slack L-U among uncoloured (lowest values):", {v: slack_hist[v] for v in lo}, flush=True)
