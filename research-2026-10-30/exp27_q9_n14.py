"""exp27: conjecture Q9 on every connected quartic graph with n vertices (target n = 14, OEIS A006820 = 88168).

Q9 (ROUTE_Q section 8.4, NEW_DIRECTIONS section 2): apart from C5[2], the edges can be split into 9 classes
whose conflict graphs are bipartite with maximum degree <= 2, so chi'_s <= 18 and the "9 classes + 2 defect
colours" scheme needs no defect edge at all.  ROUTE_Q section 8.2 checked n <= 13; n = 14 was left open
because the single-process enumeration of exp10_enum would take hours.

Step 1  enumerate the isomorphism classes by the switch-BFS of exp10_enum; every BFS level is split across
        worker processes, which skip classes already seen (keys are hashes of the exact invariants; a hash
        collision could only lower the count, so agreement with A006820 still certifies completeness).
Step 2  test Q9 on every graph (solve_Q_budget, time limit per graph); a graph that is not shown to satisfy
        Q9 is tested directly for chi'_s <= 18 and chi'_s <= 20.

Step 3  (mode complete) the invariant is not complete at n = 14: the BFS finds 88166 classes, 2 short of
        A006820.  For every switch of every listed graph, look up the representatives with the same key and
        test isomorphism exactly (VF2++); a switch isomorphic to none of them is a missing class.  Repeat from
        the new classes until nothing new appears, append them to graphs_n<n>.txt and test Q9 on them.

Usage: exp27_q9_n14.py n workers [budget_seconds] [test-only | complete]
       writes graphs_n<n>.txt (test-only reads it, complete extends it)
"""
import multiprocessing as mp
import sys
import time
from collections import Counter

import networkx as nx

from exp10_enum import A006820, invariant, switches
from exp10d_slack import solve_Q_budget
from sec import colourable, conflict_graph

_SEEN = frozenset()


def _init(seen):
    global _SEEN
    _SEEN = seen


def _expand(args):
    n, graphs = args
    out = {}
    for edges in graphs:
        for h in switches(n, edges):
            k = invariant(n, h)[0]
            if k not in _SEEN and k not in out:
                out[k] = h
    return out


_KEYS = {}


def _init_complete(keys):
    global _KEYS
    _KEYS = keys


def _check(args):
    """Connected switches of the given graphs that are isomorphic to no representative with the same key."""
    n, graphs = args
    found = []
    for edges in graphs:
        for h in switches(n, edges):
            k = invariant(n, h)[0]
            H = nx.Graph(list(h))
            reps = _KEYS.get(k, [])
            if not reps and not nx.is_connected(H):
                continue
            if not any(nx.vf2pp_is_isomorphic(H, nx.Graph(list(r))) for r in reps):
                found.append((k, h))
    return found


def complete(n, workers, graphs):
    keys = {}
    for g in graphs:
        keys.setdefault(invariant(n, g)[0], []).append(g)
    new, todo, rnd = [], graphs, 0
    while todo:
        rnd += 1
        t = time.time()
        fresh = []
        chunks = [(n, todo[i:i + 50]) for i in range(0, len(todo), 50)]
        with mp.Pool(workers, initializer=_init_complete, initargs=(keys,)) as pool:
            for found in pool.imap_unordered(_check, chunks):
                for k, h in found:
                    H = nx.Graph(list(h))
                    reps = keys.setdefault(k, [])
                    if not any(nx.vf2pp_is_isomorphic(H, nx.Graph(list(r))) for r in reps):
                        reps.append(h); fresh.append(h)
        print(f"  complete round {rnd}: {len(todo)} graphs checked, {len(fresh)} new classes  "
              f"[{time.time()-t:.0f}s]", flush=True)
        new += fresh
        todo = fresh
    return new


def enumerate_par(n, workers):
    G0 = nx.circulant_graph(n, [1, 2])
    start = tuple(sorted((min(u, v), max(u, v)) for u, v in G0.edges()))
    seen = {invariant(n, start)[0]: start}          # value None marks a disconnected class
    queue, level = [start], 0
    while queue:
        chunks = [(n, queue[i:i + 20]) for i in range(0, len(queue), 20)]
        nxt = []
        with mp.Pool(workers, initializer=_init, initargs=(frozenset(seen),)) as pool:
            for out in pool.imap_unordered(_expand, chunks):
                for k, h in out.items():
                    if k in seen:
                        continue
                    if nx.is_connected(nx.Graph(list(h))):
                        seen[k] = h; nxt.append(h)
                    else:
                        seen[k] = None
        level += 1
        print(f"  level {level}: {len(nxt)} new, {sum(v is not None for v in seen.values())} total", flush=True)
        queue = nxt
    return [h for h in seen.values() if h is not None]


def _test(args):
    i, edges, budget = args
    G = nx.Graph(list(edges))
    t = time.time()
    q9 = solve_Q_budget(G, 9, budget)
    res = {"i": i, "Q9": q9, "girth": nx.girth(G), "t": round(time.time() - t, 2)}
    if q9 is not True:
        H = conflict_graph(G, G.edges())
        res["chi_s<=18"] = colourable(H, 18) is not None
        res["chi_s<=20"] = colourable(H, 20) is not None
    return res


if __name__ == "__main__":
    n, workers = int(sys.argv[1]), int(sys.argv[2])
    budget = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    t0 = time.time()
    if "test-only" in sys.argv[4:] or "complete" in sys.argv[4:]:     # reuse graphs_n<n>.txt
        with open(f"graphs_n{n}.txt") as fh:
            graphs = [tuple(tuple(map(int, t.split("-"))) for t in line.split()) for line in fh]
        print(f"n={n}: loaded {len(graphs)} graphs (OEIS A006820: {A006820[n]})", flush=True)
        if "complete" in sys.argv[4:]:
            new = complete(n, workers, graphs)
            total = len(graphs) + len(new)
            print(f"n={n}: {len(new)} missing classes found, {total} in all (OEIS A006820: {A006820[n]}) "
                  f"{'complete' if total == A006820[n] else 'MISMATCH'}", flush=True)
            for h in new:
                print(f"   new class: girth={nx.girth(nx.Graph(list(h)))} edges={list(h)}", flush=True)
            with open(f"graphs_n{n}.txt", "a") as fh:
                for edges in new:
                    fh.write(" ".join(f"{u}-{v}" for u, v in edges) + "\n")
            graphs = new                                # step 2 below tests only the new classes
    else:
        graphs = enumerate_par(n, workers)
        ok = len(graphs) == A006820[n]
        print(f"n={n}: {len(graphs)} classes (OEIS A006820: {A006820[n]}) {'complete' if ok else 'MISMATCH'}"
              f"  [{time.time()-t0:.0f}s]", flush=True)
        with open(f"graphs_n{n}.txt", "w") as fh:
            for edges in graphs:
                fh.write(" ".join(f"{u}-{v}" for u, v in edges) + "\n")
    if not graphs:
        sys.exit()
    t1 = time.time()
    with mp.Pool(workers) as pool:
        results = pool.map(_test, [(i, e, budget) for i, e in enumerate(graphs)], chunksize=16)
    verdict = Counter({True: "yes", False: "no", None: "unknown"}[r["Q9"]] for r in results)
    slow = max(results, key=lambda r: r["t"])
    print(f"n={n}: Q9 on {len(results)} graphs: {dict(verdict)}  [{time.time()-t1:.0f}s]", flush=True)
    print(f"   girth counts: {dict(sorted(Counter(r['girth'] for r in results).items()))}; "
          f"slowest Q9 call {slow['t']}s (#{slow['i']})", flush=True)
    for r in results:
        if r["Q9"] is not True:
            print(f"   NOT Q9 #{r['i']}: {r}  edges={graphs[r['i']]}", flush=True)
