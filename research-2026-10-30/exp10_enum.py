"""Experiment 10a: enumerate all connected 4-regular graphs on n vertices (no nauty needed).

Connected graphs with a fixed degree sequence are connected under double-edge switches that keep
the graph connected (Taylor 1981), so a BFS over isomorphism classes from one start graph reaches
every class.  Classes are told apart by exact integer invariants (traces of matrix powers, which
fix the spectra, plus per-vertex and per-edge walk counts).  A collision of two classes could only
make the final count smaller, so agreement with OEIS A006820 certifies the list is complete.

Output: graphs_n<N>.txt, one graph per line as a space-separated edge list."""
import sys
import time

import networkx as nx
import numpy as np

A006820 = {5: 1, 6: 1, 7: 2, 8: 6, 9: 16, 10: 59, 11: 265, 12: 1544, 13: 10778, 14: 88168}


def invariant(n, edges):
    A = np.zeros((n, n), dtype=np.int64)
    for u, v in edges:
        A[u, v] = A[v, u] = 1
    A2 = A @ A
    B = A * A2                     # common-neighbour counts on edges
    C = A * (A2 @ A2)              # 4-walk counts on edges
    out = []
    for M in (A, B, C):
        P = np.eye(n, dtype=np.int64)
        tr = []
        for _ in range(n):
            P = P @ M
            tr.append(int(np.trace(P)))
        out.append(tuple(tr))
    P = A2.copy()
    diag = [np.diag(A2)]
    for _ in range(4):
        P = P @ A
        diag.append(np.diag(P))
    out.append(tuple(sorted(zip(*[d.tolist() for d in diag]))))
    out.append(tuple(sorted(int(B[u, v]) * 1000 + int(C[u, v]) for u, v in edges)))
    return hash(tuple(out)), tuple(out)


def switches(n, edges):
    E = set(edges)
    el = list(edges)
    for i in range(len(el)):
        a, b = el[i]
        for j in range(i + 1, len(el)):
            c, d = el[j]
            if len({a, b, c, d}) < 4:
                continue
            for (p, q), (r, s) in (((a, c), (b, d)), ((a, d), (b, c))):
                e1, e2 = (min(p, q), max(p, q)), (min(r, s), max(r, s))
                if e1 in E or e2 in E:
                    continue
                yield tuple(sorted((E - {el[i], el[j]}) | {e1, e2}))


def enumerate_quartic(n):
    G0 = nx.circulant_graph(n, [1, 2])
    start = tuple(sorted((min(u, v), max(u, v)) for u, v in G0.edges()))
    seen = {invariant(n, start)[1]: start}
    queue = [start]
    while queue:
        nxt = []
        for edges in queue:
            for h in switches(n, edges):
                key = invariant(n, h)[1]
                if key in seen:
                    continue
                if not nx.is_connected(nx.Graph(list(h))):
                    continue
                seen[key] = h
                nxt.append(h)
        queue = nxt
    return list(seen.values())


if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        t0 = time.time()
        graphs = enumerate_quartic(n)
        ok = len(graphs) == A006820[n]
        print(f"n={n}: {len(graphs)} classes (OEIS A006820: {A006820[n]}) {'complete' if ok else 'MISMATCH'}"
              f"  [{time.time()-t0:.0f}s]", flush=True)
        with open(f"graphs_n{n}.txt", "w") as fh:
            for edges in graphs:
                fh.write(" ".join(f"{u}-{v}" for u, v in edges) + "\n")
