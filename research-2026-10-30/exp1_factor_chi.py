"""Experiment 1: max chi(H_F) over sampled 2-factors F of 4-regular graphs,
including graphs with short cycles (the archive only studied girth >= 5)."""
import json
import random
import sys
import time

import networkx as nx

from sec import blowup_cycle, chromatic, conflict_graph, random_two_factorization


def circulant(n, jumps):
    return nx.circulant_graph(n, jumps)


def families():
    yield "C5[2]", blowup_cycle(5)
    for k in (6, 7, 8, 9, 11):
        yield f"C{k}[2]", blowup_cycle(k)
    for n in range(11, 31):
        for a in range(1, n // 2):
            for b in range(a + 1, (n + 1) // 2):
                G = circulant(n, [a, b])
                if nx.is_connected(G) and all(d == 4 for _, d in G.degree()):
                    yield f"Circ{n}({a},{b})", G
    rng = random.Random(20261029)
    for n in list(range(11, 41)) * 8:
        G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
        if nx.is_connected(G):
            yield f"rand{n}", G


def main(samples=25, out="exp1_results.json"):
    rng = random.Random(1)
    results = []
    worst = 0
    t0 = time.time()
    for name, G in families():
        best = 0
        bestF = None
        girth = nx.girth(G)
        for _ in range(samples):
            F1, F2 = random_two_factorization(G, rng)
            for F in (F1, F2):
                c = chromatic(conflict_graph(G, F))
                if c > best:
                    best, bestF = c, F
        results.append({"name": name, "n": G.number_of_nodes(), "girth": girth, "max_chi_HF": best})
        if best >= worst:
            worst = best
            print(f"{name:18s} n={G.number_of_nodes():3d} girth={girth} max chi(H_F)={best}  [{time.time()-t0:.0f}s]", flush=True)
        if best >= 11:
            print("  *** chi(H_F) >= 11 ***", name, sorted(bestF), flush=True)
    json.dump(results, open(out, "w"), indent=1)
    from collections import Counter
    print("distribution:", Counter(r["max_chi_HF"] for r in results))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 25)
