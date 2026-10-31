"""exp30: does L^2(G) always split into 8 classes of maximum degree <= 2?  (Brooks-type partition, Sigma(d+1) = 24.)

Lovasz's partition lemma needs Sigma(d_i + 1) >= Delta(L^2) + 1 = 25, which is why the "9 classes + 2 defect
colours" scheme (NEW_DIRECTIONS section 1) uses 9 classes of degree <= 2.  Brooks-type partition theorems
lower the requirement to Sigma(d_i + 1) >= Delta when the graph has no K_{Delta+1}; L^2 of a Delta = 4 graph
has clique number <= 20 < 25.  If 8 classes of degree <= 2 always exist, the scheme becomes "8 classes +
4 defect colours" (16 + 4 = 20), with far more room for the defects than 9 + 2.

This script only tests existence, by SAT, on every connected quartic graph with n vertices (graphs_n<n>.txt),
and prints every graph that fails.  It also reports how many of the 8-class partitions found have no odd class
cycle (then chi'_s <= 16) -- only a by-product, the solver is not asked to avoid odd cycles.

Usage: exp30_brooks8.py n1,n2,... [workers] [K] [d]
       exp30_brooks8.py random n g seed K1,K2,...     (one random quartic graph of girth g, d = 2)
"""
import sys
import time
from collections import Counter
from multiprocessing import Pool

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from exp10_testQ import load
from sec import conflict_graph


def partition(G, K=8, d=2):
    E = list(G.edges())
    H = conflict_graph(G, E)
    idx = {e: i for i, e in enumerate(H)}
    pool = IDPool()
    x = lambda i, c: pool.id(("x", i, c))
    cl = []
    for e, i in idx.items():
        cl.append([x(i, c) for c in range(K)])
    cl.append([x(0, 0)])
    for e, i in idx.items():
        nb = [idx[f] for f in H[e]]
        if len(nb) <= d:
            continue
        for c in range(K):
            enc = CardEnc.atmost([x(j, c) for j in nb], bound=d, vpool=pool, encoding=EncType.seqcounter)
            cl += [[-x(i, c)] + c2 for c2 in enc.clauses]
    with Solver(name="cd15", bootstrap_with=cl) as s:
        if not s.solve():
            return None
        pos = set(l for l in s.get_model() if l > 0)
    cls = {e: next(c for c in range(K) if x(i, c) in pos) for e, i in idx.items()}
    odd = 0
    for c in range(K):
        S = H.subgraph([e for e in H if cls[e] == c])
        odd += sum(1 for comp in nx.connected_components(S) if len(comp) % 2 and len(comp) >= 3
                   and all(S.degree(v) == 2 for v in comp))
    return odd


def test(args):
    i, G, K, d = args
    t = time.time()
    r = partition(G, K, d)
    return i, r, round(time.time() - t, 2)


def random_mode(n, g, seed, Ks):
    import random
    from exp5b_high_girth import raise_girth
    G = nx.random_regular_graph(4, n, seed=seed)
    raise_girth(G, g, random.Random(seed), rounds=200)
    for K in Ks:
        t = time.time()
        r = partition(G, K, 2)
        print(f"random n={n} girth={nx.girth(G)} seed={seed}: K={K} classes of degree <= 2 "
              f"{'exist' if r is not None else 'DO NOT EXIST'}; odd class cycles in the found partition: {r}  "
              f"[{time.time()-t:.1f}s]", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "random":
        random_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), [int(v) for v in sys.argv[5].split(",")])
        sys.exit()
    ns = [int(v) for v in sys.argv[1].split(",")]
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    d = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    for n in ns:
        t0 = time.time()
        graphs = load(n)
        with Pool(workers) as pool:
            res = pool.map(test, [(i, G, K, d) for i, G in enumerate(graphs)], chunksize=8)
        fails = [i for i, r, _ in res if r is None]
        odd = Counter(min(r, 3) for _, r, _ in res if r is not None)
        slow = max(res, key=lambda t: t[2])
        print(f"n={n}: {len(graphs)} graphs, K={K} classes of degree <= {d}: fails on {len(fails)}; "
              f"odd class cycles in the found partition (0/1/2/3+): {dict(sorted(odd.items()))}; "
              f"slowest {slow[2]}s  [{time.time()-t0:.0f}s]", flush=True)
        for i in fails:
            G = graphs[i]
            print(f"   FAIL n={n} #{i}: girth={nx.girth(G)} edges={sorted(G.edges())}", flush=True)
