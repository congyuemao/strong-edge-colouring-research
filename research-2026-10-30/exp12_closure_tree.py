"""Experiment 12: "closure paths are stuck too" (Lemma 11) in the local model.

Lemma 11 (lex-min of (Phi1, Phi2)).  Let e lie on an odd cycle, j a zero-cost class of e, P the
closure path, p an interior vertex of P.  Then for every zero-cost class k of p, the two
k-neighbours of p are the two ends of one even path.  (Otherwise: move p into k -- Phi1 and Phi2
unchanged, P is cut -- then move e into j -- no new odd cycle, the old one is destroyed.)
Depth 2: if q is an interior vertex of p's closure path in class k, the same holds for q's zero-cost
classes m != j (m = j could re-close P, so it is excluded).

Also used: R3/R4 hold at the zero-cost closures of EVERY own-degree-2 edge (they only use Phi1),
so they are imposed at the level-1/level-2 edges as well.

Encoded on top of exp11 (pair variables with at-most-one partner, no triangles in any class).
In the ball we only see the path neighbour of each closure end: p = the unique class-j neighbour
of an end x when that neighbour has class-j degree 2."""
import itertools
import sys
import time

from exp8_local_sat import pair_types
from exp9_potentials import Model, nbset
from exp11_pairing import Pairs, closure_pairs, cycle_conditions_g


def interior_links(M, src_lit, e, own, banned):
    """For edge e (on a stuck structure whenever src_lit holds) and each zero-cost class j of e
    (j != own, j not in banned): yield (j, p, cond) where cond = list of literals meaning
    "x is a j-neighbour of e (a closure end), p is x's path neighbour and is interior"."""
    x = M.x
    for j in range(M.K):
        if j == own or j in banned:
            continue
        Dj = M.degree_lits(e, j)
        for xe in M.nbrs(e):
            if not M.complete(xe):
                continue
            for p in M.nbrs(xe):
                if p == e or p in nbset(M, e) or not M.complete(p):
                    continue
                Dp = M.degree_lits(p, j)
                yield j, p, [src_lit, x[xe, j], -Dj[3], x[p, j], Dp[2]]


def stuck_vertex(M, pairs, v, own, guard_lit, banned):
    """v (class own, own-degree 2) is on a stuck structure whenever guard_lit holds:
    R1/R3/R4 plus every zero-cost closure is a pair of ends of one even path (classes in
    `banned` exempt from the pair condition)."""
    cycle_conditions_g(M, v, own, [guard_lit], [])
    closure_pairs(M, v, own, [guard_lit],
                  lambda j, n, m: True if j in banned else pairs.lit(j, n, m))


def build(R, K, f, g, opts):
    M = Model(R, K)
    M.TRUE = M.new()
    M.s.add_clause([M.TRUE])
    M.r1 = set()
    M.base = M
    e0 = (0, 1)
    s, x = M.s, M.x
    pairs = Pairs(M)
    pairs.nouniq, pairs.noP3 = "nouniq" in opts, False
    N0 = M.nbrs(e0)
    for e in (e0, f, g):
        s.add_clause([x[e, 0]])
    for n in N0:
        if n not in (f, g):
            s.add_clause([-x[n, 0]])
    cyc = (e0, f, g)
    for e in cyc:
        D0 = M.degree_lits(e, 0)
        s.add_clause([D0[2]])
        s.add_clause([-D0[3]])
        stuck_vertex(M, pairs, e, 0, M.TRUE, ())
    if "notri" not in opts:
        near = [w for w in M.E if M.edepth(w) <= 3]
        nearset = set(near)
        for a in near:
            for b in nbset(M, a):
                if b <= a or b not in nearset:
                    continue
                for c in nbset(M, a) & nbset(M, b):
                    if c <= b or c not in nearset:
                        continue
                    for k in range(K):
                        s.add_clause([-x[a, k], -x[b, k], -x[c, k]])
    depth = 2 if "depth2" in opts else 1
    level = {(e, 0): M.TRUE for e in cyc}   # (edge, its class) -> literal "edge is stuck"
    banned_of = {(e, 0): () for e in cyc}
    for d in range(depth):
        new = {}
        new_banned = {}
        for (v, own), lit in level.items():
            for j, p, cond in interior_links(M, lit, v, own, ()):
                key = (p, j)
                if key not in new:
                    new[key] = M.new()
                    # banned classes for p's own closures: depth 1 none; depth 2 the class of
                    # the path that v itself closes (v's own class when v is level 1)
                    new_banned[key] = () if d == 0 else (own,)
                s.add_clause([-c for c in cond] + [new[key]])
        for key, lit in new.items():
            p, j = key
            stuck_vertex(M, pairs, p, j, lit, new_banned[key])
        level, banned_of = new, new_banned
    pairs.finish()
    M.npairs = len(pairs.pi)
    return M


if __name__ == "__main__":
    K, R = int(sys.argv[1]), int(sys.argv[2])
    opts = set(sys.argv[3].split(",")) if len(sys.argv) > 3 and sys.argv[3] else set()
    only = sys.argv[4].split(";") if len(sys.argv) > 4 else None
    for name, (f, g) in pair_types().items():
        if only and name not in only:
            continue
        if g in nbset(Model(3, 1), f):
            continue
        t0 = time.time()
        M = build(R, K, f, g, opts)
        tb = time.time() - t0
        ok = M.s.solve()
        print(f"K={K} R={R} {','.join(sorted(opts)) or 'base'}  {name:16s}: {'SAT' if ok else 'UNSAT'}"
              f"  vars={M.top} pairs={M.npairs} [build {tb:.0f}s, total {time.time()-t0:.0f}s]", flush=True)
        M.s.delete()
