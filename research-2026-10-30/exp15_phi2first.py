"""Experiment 15: the reordered potential -- among partitions with every class of L^2-max-degree <= 2,
minimise Phi2 (odd-cycle components) first and Phi1 (in-class conflicts) second.  Periodic test of
exp14 under the new stuck conditions.

Why: under (Phi1, Phi2) the parity-changing detour costs one conflict and is never an improvement
(ROUTE_Q_zh.md 9.5), and exp14 showed the stuck structure then repeats with odd period (case (c)).

Stuck conditions at a lex-min of (Phi2, Phi1) over max-degree-<=2 partitions:
  S    e on the odd cycle C (class 0), class j != 0: moving e to j would destroy C, so it is
       infeasible or recreates an odd cycle:  d_j(e) >= 3,  or a j-neighbour of e has j-degree 2
       (blocked),  or d_j(e) = 2 with both j-neighbours path ends (the closure).
  R1'  any edge y of own degree a, class j with d_j(y) < a: the move must be blocked (else Phi1
       drops and, as d_j(y) <= 1, no odd cycle is created).
  maxd every class has max degree <= 2 (hard constraint of the space).
  det  parity detours: replace a segment of C (1 or 2 consecutive edges) by a path W of other
       edges of length one more / one less, so that C becomes an EVEN cycle; the segment edges go
       to classes where they have <= 1 neighbour.  If feasible, Phi2 drops -- so every detour,
       for every choice of destinations, must violate max degree somewhere.
  flip (optional) when the closure condition holds, e moved into j is again a minimum; the new
       odd cycle through e and its j-neighbours must satisfy S.
No-triangle (Lemmas 7, 9) is NOT assumed: those lemmas were proved for the old potential."""
import itertools
import sys
import time

from exp14_periodic import PModel, PState
from exp9_potentials import nbset


def deg(S, e, c):
    return S.degree_lits(e, c, 4)


def blocked(S, e, j, cache):
    """Literal b -> some j-neighbour of e has j-degree 2 (unknown degrees count as possibly 2)."""
    key = (id(S), e, j)
    if key in cache:
        return cache[key]
    M = S.base if isinstance(S, PState) else S
    b = M.new()
    opts = []
    for n in S.nbrs(e):
        a = M.new()
        S.s.add_clause([-a, S.x[n, j]])
        if S.complete(n):
            S.s.add_clause([-a, deg(S, n, j)[2]])
        opts.append(a)
    S.s.add_clause([-b] + opts)
    cache[key] = b
    return b


def closure(S, e, j):
    """Literal t -> d_j(e) = 2 and both j-neighbours of e have j-degree exactly 1."""
    M = S.base if isinstance(S, PState) else S
    t = M.new()
    D = deg(S, e, j)
    S.s.add_clause([-t, D[2]])
    S.s.add_clause([-t, -D[3]])
    for n in S.nbrs(e):
        if S.complete(n):
            Dn = deg(S, n, j)
            S.s.add_clause([-t, -S.x[n, j], Dn[1]])
            S.s.add_clause([-t, -S.x[n, j], -Dn[2]])
    return t


def s_cond(S, e, own, guard, cache):
    neg = [-l for l in guard]
    out = {}
    for j in range(S.K):
        if j == own:
            continue
        t = closure(S, e, j)
        S.s.add_clause(neg + [deg(S, e, j)[3], blocked(S, e, j, cache), t])
        out[j] = t
    return out


def r1prime(S, y, cache):
    x = S.x
    for i in range(S.K):
        Di = deg(S, y, i)
        S.s.add_clause([-x[y, i], -Di[3]])
        for j in range(S.K):
            if j == i:
                continue
            Dj = deg(S, y, j)
            S.s.add_clause([-x[y, i], -Di[1], Dj[1]])
            S.s.add_clause([-x[y, i], -Di[2], Dj[2], blocked(S, y, j, cache)])


def free_lit(M, r, m, cache):
    """Literal f -> r can join class m without creating a cycle or a degree-3 vertex:
    deg_m(r) <= 1 and every m-neighbour of r has m-degree <= 1 (base-state counts, which can only
    over-estimate the degrees in the compound move -- so certified improvements are genuine)."""
    key = ("free", r, m)
    if key in cache:
        return cache[key]
    f = M.new()
    M.s.add_clause([-f, -deg(M, r, m)[2]])
    for z in M.nbrs(r):
        if not M.complete(z):
            M.s.add_clause([-f, -M.x[z, m]])
        else:
            M.s.add_clause([-f, -M.x[z, m], -deg(M, z, m)[2]])
    cache[key] = f
    return f


def compound(M, e, cache):
    """Clear-then-move.  e on C (class 0), class j:
      (a) d_j(e) = 1, its j-neighbour n has j-degree 2 with j-neighbour r (r not adjacent to e):
          move r to a free class m, then e to j  (e gets one neighbour, n stays at degree 2);
      (b) d_j(e) = 2 with j-neighbours n1, n2: move n1 to a free class m, then e to j, provided
          n2 then has j-degree <= 1 (it loses n1 if adjacent).
    Each drops Phi2 by one, so neither may be available."""
    x, K = M.x, M.K
    Ne = M.nbrs(e)
    for j in range(1, K):
        De = deg(M, e, j)
        for n in Ne:
            if not M.complete(n):
                continue
            Dn = deg(M, n, j)
            for r in M.nbrs(n):
                if r == e or r in nbset(M, e) or M.in_cycle(r) or not M.complete(r):
                    continue
                for m in range(K):
                    if m == j:
                        continue
                    if m == 0 and any(M.in_cycle(z) for z in M.nbrs(r)):
                        continue
                    M.s.add_clause([-x[n, j], De[2], -x[r, j], -free_lit(M, r, m, cache)])
            for n2 in Ne:
                if n2 == n or not M.complete(n2):
                    continue
                D2 = deg(M, n2, j)
                for m in range(K):
                    if m == j or (m == 0 and any(M.in_cycle(z) for z in M.nbrs(n) if z != e)):
                        continue
                    if m == 0 and e in nbset(M, n):
                        pass  # e leaves class 0, so n's class-0 count over-estimates: still sound
                    # after n leaves: n2's j-degree is D2 - [n ~ n2]; require it <= 1
                    need = D2[2] if n2 not in nbset(M, n) else D2[3]
                    M.s.add_clause([-x[n, j], -x[n2, j], -De[2], De[3], need,
                                    -free_lit(M, n, m, cache)])


def detours(M, cyc_all):
    """Parity detours around each base cycle edge: (segment, W)."""
    inC = M.in_cycle
    out = []
    for c in cyc_all:
        cn = [n for n in M.nbrs(c) if inC(n)]
        for A, B in itertools.permutations(cn, 2):
            # k = 1: replace c by w1 - w2
            if A < B:
                for w1 in M.nbrs(A):
                    if inC(w1) or B in nbset(M, w1):
                        continue
                    for w2 in nbset(M, w1):
                        if inC(w2) or w2 not in nbset(M, B) or A in nbset(M, w2):
                            continue
                        W = (w1, w2)
                        if ok_path(M, W, {A, B, c}):
                            out.append(((c,), W))
            # k = 2: replace (c, B) by w  or by w1 - w2 - w3, between A and B' (B's other C-nbr)
            Bn = [n for n in M.nbrs(B) if inC(n) and n != c]
            if len(Bn) != 1 or not (c < B):
                continue
            B2 = Bn[0]
            ends = {A, B2, c, B}
            for w in M.nbrs(A):
                if not inC(w) and w in nbset(M, B2) and ok_path(M, (w,), ends):
                    out.append(((c, B), (w,)))
            for w1 in M.nbrs(A):
                if inC(w1) or B2 in nbset(M, w1):
                    continue
                for w3 in M.nbrs(B2):
                    if inC(w3) or A in nbset(M, w3) or w3 in nbset(M, w1) or w3 == w1:
                        continue
                    for w2 in nbset(M, w1) & nbset(M, w3):
                        if inC(w2) or A in nbset(M, w2) or B2 in nbset(M, w2):
                            continue
                        W = (w1, w2, w3)
                        if ok_path(M, W, ends):
                            out.append(((c, B), W))
    return out


def ok_path(M, W, allowed):
    """W edges complete, not on C except next to `allowed` C-edges."""
    for w in W:
        if not M.complete(w) or M.edepth(w) > 3:
            return False
        for n in M.nbrs(w):
            if M.in_cycle(n) and n not in allowed:
                return False
    return True


def no_improving_detour(M, seg, W):
    """For every destination tuple of the segment edges, the detour violates max degree."""
    K = M.K
    for dest in itertools.product(range(1, K), repeat=len(seg)):
        over = {s: m for s, m in zip(seg, dest)}
        over.update({w: 0 for w in W})
        F = PState(M, over)
        viol = [deg(F, w, 0)[3] for w in W]
        for s, m in over.items():
            if m == 0:
                continue
            viol.append(deg(F, s, m)[2])      # s would close a cycle / have 2 neighbours
            for n in F.nbrs(s):
                if n in over:
                    continue
                v = M.new()
                M.s.add_clause([-v, F.x[n, m]])
                if F.complete(n):
                    M.s.add_clause([-v, deg(F, n, m)[3]])
                viol.append(v)
        M.s.add_clause(viol)


def build(pattern, L, D, opts):
    K = 10
    M = PModel(pattern, L, D, K)
    s, x = M.s, M.x
    cache = {}
    cyc = [e for e in M.base_edges(1) if M.in_cycle(e)]
    for e in cyc:
        s.add_clause([x[e, 0]])
        for n in M.nbrs(e):
            if not M.in_cycle(n):
                s.add_clause([-x[n, 0]])
    for y in M.base_edges(3):
        r1prime(M, y, cache)
    closures = {}
    for e in cyc:
        closures[e] = s_cond(M, e, 0, [], cache)
    if "cmp" in opts:
        for e in cyc:
            compound(M, e, cache)
    if "det" in opts:
        dets = detours(M, cyc)
        M.ndet = len(dets)
        for seg, W in dets:
            no_improving_detour(M, seg, W)
    else:
        M.ndet = 0
    if "flip" in opts:
        for e in cyc:
            for j, t in closures[e].items():
                V = PState(M, {e: j})
                s_cond(V, e, j, [t], cache)
                for n in M.nbrs(e):
                    if not M.in_cycle(n) and M.complete(n):
                        s_cond(V, n, j, [t, x[n, j]], cache)
    return M


if __name__ == "__main__":
    pattern = sys.argv[1]
    Ls = [int(v) for v in sys.argv[2].split(",")]
    D = int(sys.argv[3])
    opts = set(sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    for L in Ls:
        t0 = time.time()
        M = build(pattern, L, D, opts)
        tb = time.time() - t0
        ok = M.s.solve()
        print(f"pattern={pattern:2s} L={L} D={D} {','.join(sorted(opts)) or 'base'}: "
              f"{'SAT' if ok else 'UNSAT'}  detours={M.ndet} vars={M.top} "
              f"[build {tb:.0f}s, total {time.time()-t0:.0f}s]", flush=True)
        M.s.delete()
