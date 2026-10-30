"""exp20c: glue tight quartic graphs along 2-edge cuts and recompute the exact 4-matching budget.

Gluing A and B: delete an edge a1a2 of A and an edge b1b2 of B, add a1b1 and a2b2.  The result is
quartic with a 2-edge cut; in every 4-edge-colouring both cut edges get the same colour, since each
side has an even number of vertices.  The n = 18 extremal graph of exp20 is such a gluing of n = 10
#51, so gluing is the natural way to look for B* >= 21.

Pieces: the graphs with B* >= 19 from exp19 (n = 10 #35, #51, #57, #58 = C5[2]; n = 12 #1528,
#1529) and the n = 14 extremal graph from exp20.  Every pair of pieces (with repetition), every
edge of each, and both ways of crossing are tried.  Any graph with B* >= 21 is then checked for the
5-matching form at budget 20 by SAT.

Usage: exp20c_glue.py
"""
import itertools
import multiprocessing as mp
import time

import networkx as nx

from exp19_property_m import load, property_m
from exp20_search import analyse

N14 = [(0, 3), (0, 7), (0, 8), (0, 9), (1, 2), (1, 4), (1, 12), (2, 6), (2, 13), (3, 2), (3, 4), (3, 5),
       (4, 10), (4, 11), (5, 10), (6, 10), (7, 6), (7, 11), (7, 12), (8, 1), (8, 10), (8, 13), (9, 6),
       (9, 11), (9, 12), (12, 5), (13, 5), (13, 11)]


def pieces():
    g10, g12 = list(load(10)), list(load(12))
    out = {f"n10#{i}": nx.Graph(g10[i]) for i in (35, 51, 57, 58)}
    out.update({f"n12#{i}": nx.Graph(g12[i]) for i in (1528, 1529)})
    out["n14*"] = nx.Graph(N14)
    return out


def edge_orbit_reps(G):
    """One edge from each orbit of Aut(G) acting on edges (keeps the search small)."""
    autos = list(nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter())
    seen, reps = set(), []
    for u, v in G.edges():
        e = frozenset((u, v))
        if e in seen:
            continue
        reps.append((u, v))
        for a in autos:
            seen.add(frozenset((a[u], a[v])))
    return reps


def glue(A, ea, B, eb, cross):
    A = nx.relabel_nodes(A, {v: ("a", v) for v in A}); B = nx.relabel_nodes(B, {v: ("b", v) for v in B})
    G = nx.union(A, B)
    a1, a2 = ("a", ea[0]), ("a", ea[1])
    b1, b2 = ("b", eb[0]), ("b", eb[1])
    if cross:
        b1, b2 = b2, b1
    G.remove_edges_from([(a1, a2), (b1, b2)]); G.add_edges_from([(a1, b1), (a2, b2)])
    return nx.convert_node_labels_to_integers(G)


def job(args):
    na, nb, ea, eb, cross, A, B = args
    G = glue(A, ea, B, eb, cross)
    r = analyse(G)
    m5 = None
    if r is None or r[0] >= 21:
        m5 = property_m(list(G.edges()), 5, 20, budget=2_000_000)
    return na, nb, ea, eb, cross, G.number_of_nodes(), r, m5


if __name__ == "__main__":
    t0 = time.time()
    P = pieces()
    reps = {k: edge_orbit_reps(G) for k, G in P.items()}
    for k in P:
        print(f"{k}: n={P[k].number_of_nodes()} B*={analyse(P[k])[0]} edge orbits={len(reps[k])}", flush=True)
    tasks = [(na, nb, ea, eb, cross, P[na], P[nb])
             for na, nb in itertools.combinations_with_replacement(sorted(P), 2)
             for ea in reps[na] for eb in reps[nb] for cross in (False, True)]
    print(f"{len(tasks)} gluings", flush=True)
    hist, worst = {}, []
    with mp.Pool() as pool:
        for na, nb, ea, eb, cross, n, r, m5 in pool.imap_unordered(job, tasks, chunksize=4):
            key = (na, nb)
            b = r[0] if r else "class2"
            hist.setdefault(key, {}).setdefault(b, 0)
            hist[key][b] += 1
            if r is None or r[0] >= 20:
                worst.append((b, na, nb, ea, eb, cross, n, m5))
    for key in sorted(hist):
        print(key, dict(sorted(hist[key].items(), key=lambda kv: str(kv[0]))), flush=True)
    over = [w for w in worst if w[0] == "class2" or w[0] >= 21]
    print("gluings with B* >= 21 or class 2 (B*, A, B, edge A, edge B, crossed, n, M5@20):", over[:40],
          f"({len(over)} total)")
    print("gluings with B* = 20:", sum(1 for w in worst if w[0] == 20))
    print(f"[{time.time() - t0:.0f}s]")
