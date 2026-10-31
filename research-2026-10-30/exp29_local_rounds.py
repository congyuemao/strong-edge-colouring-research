"""exp29: how fast does a LOCAL (synchronous, bounded-round) Lovasz descent clean up?  Medium-girth route idea.

Idea (9 + 2 at medium girth without lex-minimality): run a T-round local rule from a random 9-partition, then
put the residual bad edges B (class-degree >= 3, or on a class cycle) into the 2 spare colours.  If L^2[B]
has maximum degree <= 1 it is 2-colourable, the classes minus B have degree <= 2 and no cycles left through
B-free edges... (cycles are put into B), so chi'_s <= 20.  A Lovasz Local Lemma version needs
P(e in B with >= 2 B-conflicts) far below 1/(e * D), D = number of events within the dependency radius,
which grows like 3^(2 * radius).  MANUSCRIPT 8.3 found that a 20-colour nibble fails this test (failure only
x7-40 smaller per round against x6561 more dependency).  This script measures the same numbers for the
9-class descent on a large random graph of girth g (a stand-in for the 4-regular tree).

Rule per round: every edge is active independently with probability `act`; an active edge whose own
class-count exceeds the minimum over classes moves to a uniformly random minimising class; all moves of a
round use the counts at the start of the round (synchronous, so the outcome after T rounds is a function
of the initial randomness within bounded distance).

Usage: exp29_local_rounds.py n g seed rounds [K] [act]
"""
import random
import sys
import time
from collections import Counter

import networkx as nx

from exp4_local_search import conflict_adj
from exp5b_high_girth import raise_girth


def stats(adj, part, K):
    m = len(adj)
    cnt = [Counter(part[w] for w in adj[i]) for i in range(m)]
    own = [cnt[i][part[i]] for i in range(m)]
    # class cycles: components whose every vertex has own == 2
    incyc = [False] * m
    seen = [False] * m
    for i in range(m):
        if seen[i] or own[i] == 0:
            continue
        comp, st = [i], [i]
        seen[i] = True
        while st:
            v = st.pop()
            for w in adj[v]:
                if part[w] == part[i] and not seen[w]:
                    seen[w] = True; comp.append(w); st.append(w)
        if all(own[v] == 2 for v in comp):
            for v in comp:
                incyc[v] = True
    B = [own[i] >= 3 or incyc[i] for i in range(m)]
    bdeg = [sum(B[w] for w in adj[i]) if B[i] else -1 for i in range(m)]
    return {"own>=3": sum(o >= 3 for o in own) / m, "on class cycle": sum(incyc) / m,
            "B": sum(B) / m, "B with >=1 B-nbr": sum(d >= 1 for d in bdeg) / m,
            "B with >=2 B-nbrs": sum(d >= 2 for d in bdeg) / m,
            "own dist": dict(sorted(Counter(own).items()))}


def run(n, g, seed, rounds, K=9, act=0.5):
    rng = random.Random(seed)
    t0 = time.time()
    G = nx.random_regular_graph(4, n, seed=seed)
    raise_girth(G, g, rng, rounds=200)
    E, adj = conflict_adj(G)
    m = len(E)
    print({"n": n, "girth": nx.girth(G), "m": m, "K": K, "act": act, "gen s": round(time.time() - t0, 1)},
          flush=True)
    part = [rng.randrange(K) for _ in range(m)]
    print({"round": 0, **stats(adj, part, K)}, flush=True)
    for r in range(1, rounds + 1):
        cnt = [Counter(part[w] for w in adj[i]) for i in range(m)]
        new = list(part)
        for i in range(m):
            if rng.random() >= act:
                continue
            c = [cnt[i][k] for k in range(K)]
            lo = min(c)
            if c[part[i]] > lo:
                new[i] = rng.choice([k for k in range(K) if c[k] == lo])
        part = new
        print({"round": r, **stats(adj, part, K)}, flush=True)


if __name__ == "__main__":
    n, g, seed, rounds = map(int, sys.argv[1:5])
    K = int(sys.argv[5]) if len(sys.argv) > 5 else 9
    act = float(sys.argv[6]) if len(sys.argv) > 6 else 0.5
    run(n, g, seed, rounds, K, act)
