"""Experiment 10b: test property Q (and, where Q fails, chi'_s <= 20) on every graph of graphs_n<N>.txt.

(Finding the least number of pairs that works was dropped: every step below it is a pigeonhole-type
UNSAT proof, which CDCL handles badly.)"""
import sys
import time
from collections import Counter
from multiprocessing import Pool

import networkx as nx

from exp3_pairs import solve_Q
from sec import colourable, conflict_graph


def load(n):
    out = []
    with open(f"graphs_n{n}.txt") as fh:
        for line in fh:
            out.append(nx.Graph([tuple(map(int, t.split("-"))) for t in line.split()]))
    return out


def test(args):
    i, G = args
    t = time.time()
    q10 = solve_Q(G, pairs=10)
    res = {"i": i, "Q10": q10, "girth": nx.girth(G), "t": time.time() - t}
    if not q10:
        H = conflict_graph(G, G.edges())
        res["chi_s<=20"] = colourable(H, 20) is not None
    return res


if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        t0 = time.time()
        graphs = load(n)
        with Pool(20) as pool:
            results = pool.map(test, list(enumerate(graphs)), chunksize=4)
        fails = [r for r in results if not r["Q10"]]
        mp = Counter(r["girth"] for r in results)
        slow = max(results, key=lambda r: r["t"])
        print(f"n={n}: {len(graphs)} graphs, Q fails on {len(fails)}  [{time.time()-t0:.0f}s]", flush=True)
        print(f"   girth counts: {dict(sorted(mp.items()))}; slowest SAT call {slow['t']:.1f}s (#{slow['i']})", flush=True)
        for r in fails:
            G = graphs[r["i"]]
            print(f"   FAIL #{r['i']}: girth={r['girth']} chi_s<=20={r['chi_s<=20']} edges={sorted(G.edges())}", flush=True)
