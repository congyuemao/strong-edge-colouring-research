"""exp50: are star states with k >= 1 locally impossible at the level of single-edge repairs?  (NEW_DIRECTIONS 11.23)

Model: the 4-regular tree around a vertex v, down to vertex depth D.  U = k + 1 edges at v stay uncoloured (conflicts are
still judged in the whole tree, through uncoloured edges too), every other edge at depth <= D gets a colour.

Question: is there a proper 20-colouring in which, for every e in U,
  (a) e is blocked: every colour occurs on N(e);
  (b) no repair T1 exists: if p occurs on exactly one member f of N(e), then f sees every colour other than p.
UNSAT would prove that in any graph that is locally this tree, some edge of U can be inserted by recolouring one edge.
Option 'all' asks (a), (b) for one fixed e only (the others are ignored), to compare k = 0 with k >= 1.

The conflicts of the members must lie in the model, so D >= 5.  Edges at the rim have conflicts outside; only members'
conflicts are used, and those are complete.

Usage: exp50_star_local.py k [D] [one]
"""
import sys
import time
from itertools import combinations

from pysat.card import CardEnc
from pysat.solvers import Cadical195

K = 20


def tree(D):
    """Vertices 0.. in BFS order, root 0 of degree 4, others of degree 4 down to depth D; returns edges, depth."""
    edges, depth, frontier = [], {0: 0}, [0]
    n = 1
    for d in range(D):
        nxt = []
        for x in frontier:
            for _ in range(4 if x == 0 else 3):
                edges.append((x, n))
                depth[n] = d + 1
                nxt.append(n)
                n += 1
        frontier = nxt
    return edges, depth


def conflicts(edges):
    inc = {}
    for i, (a, b) in enumerate(edges):
        inc.setdefault(a, []).append(i)
        inc.setdefault(b, []).append(i)
    N = []
    for i, (a, b) in enumerate(edges):
        near = set(inc[a]) | set(inc[b])
        far = set(near)
        for j in near:
            for x in edges[j]:
                far.update(inc[x])
        far.discard(i)
        N.append(far)
    return N


def main():
    k = int(sys.argv[1])
    D = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 5
    one = "one" in sys.argv
    edges, depth = tree(D)
    m = len(edges)
    N = conflicts(edges)
    U = list(range(k + 1))                                 # the first edges in BFS order are at the root
    holes = set(U)
    coloured = [i for i in range(m) if i not in holes]
    x = {(i, c): 1 + j * K + c for j, i in enumerate(coloured) for c in range(K)}
    cl = []
    for i in coloured:
        cl.append([x[i, c] for c in range(K)])
        cl += [[-x[i, a], -x[i, b]] for a, b in combinations(range(K), 2)]
    for i in coloured:
        for j in N[i]:
            if j > i and j not in holes:
                cl += [[-x[i, c], -x[j, c]] for c in range(K)]
    targets = U[:1] if one else U
    for e in targets:
        mem = sorted(N[e] - holes)
        for c in range(K):
            cl.append([x[f, c] for f in mem])
        for f in mem:
            others = [g for g in mem if g != f]
            nf = sorted(N[f] - holes)
            for p in range(K):
                base = [-x[f, p]] + [x[g, p] for g in others]
                for q in range(K):
                    if q != p:
                        cl.append(base + [x[h, q] for h in nf])
    # colour symmetry: value precedence along the members of the first target
    mem = sorted(N[targets[0]] - holes)
    for pos, f in enumerate(mem):
        for c in range(1, K):
            cl.append([-x[f, c]] + [x[g, c - 1] for g in mem[:pos]])
    t0 = time.time()
    print(f"k={k} D={D} one={one}: {m} edges, {len(cl)} clauses, |N(e)| coloured {len(mem)}", flush=True)
    with Cadical195(bootstrap_with=cl) as s:
        r = s.solve()
        print("SAT" if r else "UNSAT", f"{time.time() - t0:.1f} s", flush=True)
        if r:
            model = set(v for v in s.get_model() if v > 0)
            col = {i: next(c for c in range(K) if x[i, c] in model) for i in coloured}
            # independent check on vertex relations
            for i in coloured:
                for j in coloured:
                    if i < j and col[i] == col[j]:
                        a, b = edges[i], edges[j]
                        ad = any(p == q or (min(p, q), max(p, q)) in set(edges) for p in a for q in b)
                        assert not ad, (i, j)
            for e in targets:
                mem = [f for f in N[e] if f not in holes]
                assert len({col[f] for f in mem}) == K
                for f in mem:
                    if sum(col[g] == col[f] for g in mem) == 1:
                        assert len({col[h] for h in N[f] if h not in holes}) >= K - 1
            print("witness checked; colours of N(e) multiplicities:",
                  sorted(sum(col[f] == c for f in mem) for c in range(K)), flush=True)


main()
