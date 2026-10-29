"""Experiment 10d: how much room does property Q leave?  Test Q with 9 pairs (an 18-colouring whose
pair classes are bipartite of max degree 2) under a time limit per graph (seconds), on the exhaustive lists.
Result per graph: yes / no (proved) / unknown (budget hit)."""
import sys
import threading
import time
from collections import Counter
from multiprocessing import Pool

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.solvers import Glucose4

from exp10_testQ import load
from sec import conflict_graph, norm


def solve_Q_budget(G, pairs, budget):
    E = [norm(e) for e in G.edges()]
    H = conflict_graph(G, E)
    k = 2 * pairs
    idx = {e: i for i, e in enumerate(E)}
    x = lambda e, c: idx[e] * k + c + 1
    base = len(E) * k
    y = lambda e, p: base + idx[e] * pairs + p + 1
    top = base + len(E) * pairs
    s = Glucose4()
    for e in E:
        s.add_clause([x(e, c) for c in range(k)])
        for p in range(pairs):
            s.add_clause([-y(e, p), x(e, 2 * p), x(e, 2 * p + 1)])
            s.add_clause([y(e, p), -x(e, 2 * p)])
            s.add_clause([y(e, p), -x(e, 2 * p + 1)])
    for e, f in H.edges():
        for c in range(k):
            s.add_clause([-x(e, c), -x(f, c)])
    for e in E:
        nb = list(H[e])
        if len(nb) <= 2:
            continue
        for p in range(pairs):
            cnf = CardEnc.atmost([y(f, p) for f in nb], bound=2, top_id=top, encoding=EncType.seqcounter)
            top = max(top, cnf.nv)
            for cl in cnf.clauses:
                s.add_clause(cl + [-y(e, p)])
    s.add_clause([x(E[0], 0)])
    timer = threading.Timer(budget, s.interrupt)  # budget = seconds (pysat's conflict budget is not honoured here)
    timer.start()
    r = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    s.delete()
    return r


def test(args):
    i, G, budget = args
    r = solve_Q_budget(G, 9, budget)
    return {None: "unknown", True: "yes", False: "no"}[r], nx.girth(G)


if __name__ == "__main__":
    budget = float(sys.argv[1])
    for n in map(int, sys.argv[2:]):
        t0 = time.time()
        graphs = load(n)
        with Pool(20) as pool:
            res = pool.map(test, [(i, G, budget) for i, G in enumerate(graphs)], chunksize=4)
        print(f"n={n}: Q with 9 pairs (18 colours): {dict(Counter(r for r, _ in res))}  by girth: {dict(Counter(res))}  [{time.time()-t0:.0f}s]", flush=True)
