"""Decode a stuck bad clique from exp13: classes around X, tight classes and their K_{d_j}."""
import sys

from exp13_brooks import build, clique_types, nbset


def rel(x, y):
    """Position of conflict y relative to edge x = ab: hub at a / hub at b / triple."""
    if set(x) & set(y):
        return f"hub@{(set(x) & set(y)).pop()}"
    return "tri"


if __name__ == "__main__":
    d = [int(c) for c in sys.argv[1].split(",")]
    R, level, name = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    opts = set(sys.argv[5].split(",")) if len(sys.argv) > 5 else set()
    X = clique_types()[d[0] + 1][name]
    M = build(R, d, X, level, opts)
    assert M.s.solve()
    mod = set(l for l in M.s.get_model() if l > 0)
    cls = {e: next(c for c in range(M.K) if M.x[e, c] in mod) for e in M.E}
    deg = lambda e, c: sum(1 for y in M.nbrs(e) if cls[y] == c)
    print(f"d={d}  X={X}")
    for w in X:
        dv = [deg(w, c) for c in range(M.K)]
        eps = [dv[c] - d[c] for c in range(M.K)]
        tight = [c for c in range(1, M.K) if eps[c] == 0]
        print(f"  x={w}: deg={dv} eps={eps} tight={tight}")
        for j in tight:
            Nj = [y for y in M.nbrs(w) if cls[y] == j]
            print(f"     class {j}: N_j = {[(y, rel(w, y)) for y in Nj]}"
                  f"  inner degs {[deg(y, j) for y in Nj]}  p-degs {[deg(y, 0) for y in Nj]}")
    # how many edges of the ball (complete ones) are in bad cliques?
    bad = 0
    for e in M.E:
        if not M.complete(e):
            continue
        c = cls[e]
        N = [y for y in M.nbrs(e) if cls[y] == c]
        if len(N) == d[c] and all(b in nbset(M, a) for a in N for b in N if a < b):
            if all(M.complete(y) and deg(y, c) == d[c] for y in N):
                bad += 1
    print(f"  complete edges lying in bad cliques: {bad}")
