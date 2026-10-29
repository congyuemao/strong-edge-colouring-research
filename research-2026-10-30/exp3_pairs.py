"""Experiment 3: property Q.
Q(G): E(G) splits into 10 classes whose strong-conflict graphs are bipartite with max degree <= 2.
Q implies chi'_s(G) <= 20.  Encoded as a strong 20-colouring where colours 2p, 2p+1 form
pair p and each edge has at most 2 conflicting edges inside its own pair."""
import random
import sys
import time
from collections import Counter

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

from sec import blowup_cycle, conflict_graph, greedy_clique, norm


def solve_Q(G, pairs=10, cap=2):
    E = [norm(e) for e in G.edges()]
    H = conflict_graph(G, E)
    k = 2 * pairs
    idx = {e: i for i, e in enumerate(E)}
    x = lambda e, c: idx[e] * k + c + 1
    base = len(E) * k
    y = lambda e, p: base + idx[e] * pairs + p + 1
    top = base + len(E) * pairs
    s = Cadical153()
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
        if len(nb) <= cap:
            continue
        for p in range(pairs):
            cnf = CardEnc.atmost([y(f, p) for f in nb], bound=cap, top_id=top, encoding=EncType.seqcounter)
            top = max(top, cnf.nv)
            for cl in cnf.clauses:
                s.add_clause(cl + [-y(e, p)])
    # symmetry breaking: a clique gets colours 0,2,4,... (distinct pairs first) is not valid in
    # general, so only fix the first clique vertex's colour.
    C = greedy_clique(H)
    if C:
        s.add_clause([x(C[0], 0)])
    ok = s.solve()
    s.delete()
    return ok


def families():
    yield "C5[2]", blowup_cycle(5)
    yield "C11(1,3)", nx.circulant_graph(11, [1, 3])
    yield "K5", nx.complete_graph(5)
    yield "K4,4", nx.complete_bipartite_graph(4, 4)
    for k in (6, 7, 8, 9):
        yield f"C{k}[2]", blowup_cycle(k)
    for n in range(9, 26):
        for a in range(1, n // 2):
            for b in range(a + 1, (n + 1) // 2):
                G = nx.circulant_graph(n, [a, b])
                if nx.is_connected(G) and all(d == 4 for _, d in G.degree()):
                    yield f"Circ{n}({a},{b})", G
    rng = random.Random(7)
    for n in list(range(10, 41)) * 3:
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
        yield f"rand{n}", G


if __name__ == "__main__":
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    res = Counter()
    t0 = time.time()
    for name, G in families():
        ok = solve_Q(G, cap=cap)
        res[ok] += 1
        if not ok or name in ("C5[2]", "C11(1,3)", "K5", "K4,4"):
            print(f"{name:16s} n={G.number_of_nodes():3d} Q={'yes' if ok else 'NO'}  [{time.time()-t0:.0f}s]", flush=True)
    print("summary:", dict(res))
