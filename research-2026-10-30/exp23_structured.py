"""exp23: does property P admit the structured form 'F1 in {1,2,5}, F2 in {3,4,5}'?

Split E(G) = F1 + F2 into subgraphs of maximum degree 2 (exp18 split_two).  Variants of the
property-P SAT test of exp21:
  V1  palette restriction: edges of F1 use colours {0,1,4}, edges of F2 use {2,3,4}
      (colour 4 plays the role of the shared colour '5');
  V2  V1 plus 'along-cycle witnesses only': an edge of F_j may only use as witness the two outer
      neighbours that are its neighbours along F_j (the far ends of the adjacent F_j-edges).
V2 is the one-dimensional coupling problem: if it is satisfiable, P reduces to choosing the
shared colour class on the cycles of F1 and F2 so that the two choices never meet at a vertex.

Usage: exp23_structured.py n girth seeds
       exp23_structured.py families n girth seeds   (V2 with subsets of the constraint families)
"""
import sys
import time

from pysat.solvers import Cadical153

sys.path.insert(0, ".")
from exp18_large_girth import random_graph, girth, split_two  # noqa: E402

K = 5


def solve(adj, F, variant, budget=5_000_000, families=("F1plain", "F2plain", "shared")):
    edges = F[0] + F[1]
    fac = [0] * len(F[0]) + [1] * len(F[1])
    m = len(edges); n = len(adj)
    at = [[] for _ in range(n)]
    nbr = [[[], []] for _ in range(n)]          # neighbours of v inside F1 / F2
    for i, (u, v) in enumerate(edges):
        at[u].append(i); at[v].append(i)
        nbr[u][fac[i]].append(v); nbr[v][fac[i]].append(u)
    pal = [(0, 1, 4), (2, 3, 4)]
    x = lambda e, c: 1 + e * K + c
    miss = lambda w, c: 1 + m * K + w * K + c
    s = Cadical153()
    for e in range(m):
        s.add_clause([x(e, c) for c in pal[fac[e]]])
        for c in range(K):
            if c not in pal[fac[e]]:
                s.add_clause([-x(e, c)])
    for v in range(n):
        es = at[v]
        for i in range(len(es)):
            for j in range(i + 1, len(es)):
                for c in range(K):
                    s.add_clause([-x(es[i], c), -x(es[j], c)])
        for c in range(K):
            for f in es:
                s.add_clause([-miss(v, c), -x(f, c)])
    for e, (u, v) in enumerate(edges):
        outer = (set(adj[u]) | set(adj[v])) - {u, v}
        if len(outer) < 6:
            continue
        if variant == "V2":
            j = fac[e]
            wit = [w for w in nbr[u][j] if w != v] + [w for w in nbr[v][j] if w != u]
        else:
            wit = list(outer)
        for c in pal[fac[e]]:
            fam = "shared" if c == 4 else ("F1plain" if fac[e] == 0 else "F2plain")
            if fam in families:
                s.add_clause([-x(e, c)] + [miss(w, c) for w in wit])
    s.conf_budget(budget)
    r = s.solve_limited()
    s.delete()
    return r


def families_mode(n, g, seeds):
    """V2 with only some constraint families: F1plain (colours 1,2 on F1), F2plain (3,4 on F2),
    shared (the common colour)."""
    for seed in range(seeds):
        adj = random_graph(n, g, seed); F = split_two(adj)
        for fams in (("F1plain",), ("shared",), ("F1plain", "shared"), ("F1plain", "F2plain"),
                     ("F1plain", "F2plain", "shared")):
            t0 = time.time()
            r = solve(adj, F, "V2", budget=300000, families=fams)
            print(seed, "+".join(fams), r, f"{time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__" and sys.argv[1] == "families":
    families_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
elif __name__ == "__main__":
    n, g, seeds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for seed in range(seeds):
        adj = random_graph(n, g, seed)
        F = split_two(adj)
        cyc = []
        for j in (0, 1):
            from exp18_large_girth import components
            cyc.append(sorted(len(es) for _, es, c in components(F[j]) if c))
        row = {"seed": seed, "n": n, "girth": girth(adj), "F1 cycle lengths (min,max,count)":
               (cyc[0][0], cyc[0][-1], len(cyc[0])) if cyc[0] else None}
        for variant in ("V1", "V2"):
            t0 = time.time()
            row[variant] = solve(adj, F, variant)
            row[variant + " s"] = round(time.time() - t0, 1)
        print(row, flush=True)
