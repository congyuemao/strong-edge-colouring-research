"""Experiment 11: the local model of exp8/exp9 plus the global fact "a path has exactly two ends".

New ingredient (Vizing-fan style).  For each class k, every path endpoint has exactly one partner
(the other end of its path).  Pair variables pi[k,a,b] (a, b in the ball) express "a and b are the
two ends of one class-k path"; each endpoint has at most one partner.  Lemma 3 turns every closure
of an odd-cycle vertex into such a pair.  Flipping an odd-cycle edge e into class J changes only
classes 0 and J, so in the flipped state the pairs of every other class are the SAME variables;
that is what lets constraints from different states collide.

States encoded:
  S0        e0, f, g on a long odd cycle of class 0 (f, g = the long positions of exp8);
            no triangle in any class (Lemmas 7 and 9, girth >= 7).
  S(e,J)    for e in {e0, f, g} and every class J != 0 with d_J(e) = 2: e flipped into J.  The
            new odd cycle passes through e and its two J-neighbours n; for each such n we impose
            R1, R3, R4 and the closure pairs (classes != 0, J use the shared pi; class 0 closures
            must be the two class-0 neighbours of e, or a class-0 pair of S0).

UNSAT at a position = no long odd cycle can sit there, in graphs of large girth."""
import itertools
import sys
import time

from pysat.card import CardEnc, EncType

from exp8_local_sat import pair_types
from exp9_potentials import Model, View, cycle_conditions, nbset


class Pairs:
    def __init__(self, M):
        self.M = M
        self.pi = {}

    def lit(self, k, a, b):
        a, b = min(a, b), max(a, b)
        if (k, a, b) not in self.pi:
            M = self.M
            v = M.new()
            self.pi[k, a, b] = v
            s, x = M.s, M.x
            for c in (a, b):
                s.add_clause([-v, x[c, k]])
                if M.complete(c):
                    D = M.degree_lits(c, k)
                    s.add_clause([-v, D[1]])
                    s.add_clause([-v, -D[2]])
        return self.pi[k, a, b]

    def finish(self):
        """At most one partner per endpoint; a visible P3 end has no partner usable as a closure."""
        M, s, x = self.M, self.M.s, self.M.x
        by_end = {}
        for (k, a, b), v in self.pi.items():
            by_end.setdefault((k, a), []).append(v)
            by_end.setdefault((k, b), []).append(v)
        top = M.top
        for (k, a), lits in by_end.items():
            if len(lits) > 1 and not self.nouniq:
                cnf = CardEnc.atmost(lits, bound=1, top_id=M.top, encoding=EncType.seqcounter)
                M.top = max(M.top, cnf.nv)
                for cl in cnf.clauses:
                    s.add_clause(cl)
            if not M.complete(a) or self.noP3:
                continue
            Da = M.degree_lits(a, k)
            p3 = M.new()  # a is an end of a visible 3-vertex (odd) path
            for v in lits:
                s.add_clause([-p3, -v])
            for c in M.nbrs(a):
                if not M.complete(c):
                    continue
                Dc = M.degree_lits(c, k)
                for b in M.nbrs(c):
                    if b == a or b in nbset(M, a) or not M.complete(b):
                        continue
                    Db = M.degree_lits(b, k)
                    s.add_clause([-x[a, k], -x[c, k], -x[b, k], -Da[1], Da[2], -Dc[2], Dc[3], -Db[1], Db[2], p3])


def R1g(V, w, rguard):
    """Single-move Phi1 minimality at w in partition V, required only when all `rguard` hold
    (a flipped state is a Phi1 minimum only if the flip was zero-cost)."""
    key = (w, tuple(rguard))
    if key in V.r1:
        return
    V.r1.add(key)
    s, x, K = V.s, V.x, V.K
    neg = [-l for l in rguard]
    D = {c: V.degree_lits(w, c) for c in range(K)}
    for c in range(K):
        xc = x[w, c]
        s.add_clause(neg + [-xc, -D[c][3]])
        for c2 in range(K):
            if c2 != c:
                for k in (1, 2):
                    s.add_clause(neg + [-xc, -D[c][k], D[c2][k]])


def cycle_conditions_g(V, e, own, guard, rguard):
    """As exp9.cycle_conditions (R1, R3, R4), with R1 guarded by `rguard` and the rest by `guard`."""
    s, x, K = V.s, V.x, V.K
    neg = [-l for l in guard]
    R1g(V, e, rguard)
    for j in range(K):
        if j == own:
            continue
        Dj = V.degree_lits(e, j)
        for n in V.nbrs(e):
            if not V.complete(n):
                continue
            g1 = neg + [-x[n, j], Dj[3]]
            Dn = {c: V.degree_lits(n, c) for c in range(K)}
            R1g(V, n, rguard)
            s.add_clause(g1 + [-Dn[j][2]])
            s.add_clause(g1 + [Dn[j][1]])
            for k in range(K):
                if k not in (own, j):
                    s.add_clause(g1 + [Dn[k][2]])
            s.add_clause(g1 + [Dn[own][3]])


def closure_pairs(V, e, own, guard, P):
    """Closure {n,m} of odd-cycle vertex e in class j (d_j(e) = 2) must satisfy literal P(j,n,m)."""
    s, x, K = V.s, V.x, V.K
    neg = [-l for l in guard]
    Ne = [n for n in V.nbrs(e) if V.complete(n)]
    for j in range(K):
        if j == own:
            continue
        Dj = V.degree_lits(e, j)
        for n, m in itertools.combinations(Ne, 2):
            lit = P(j, n, m)
            if lit is True:
                continue
            s.add_clause(neg + [-x[n, j], -x[m, j], Dj[3]] + ([] if lit is False else [lit]))


def build(R, K, f, g, opts):
    M = Model(R, K)
    M.TRUE = M.new()
    M.s.add_clause([M.TRUE])
    M.r1 = set()
    M.base = M
    e0 = (0, 1)
    s, x = M.s, M.x
    pairs = Pairs(M)
    pairs.nouniq, pairs.noP3 = "nouniq" in opts, "noP3" in opts
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
    for e in cyc:
        cycle_conditions(M, e, 0, [], False, "R5" in opts)
        closure_pairs(M, e, 0, [], lambda j, n, m: pairs.lit(j, n, m))
    # Lemmas 7 + 9: no class contains an L^2-triangle (checked among edges near e0)
    near = [] if "notri" in opts else [w for w in M.E if M.edepth(w) <= 3]
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
    flips = [e0] if "e0only" in opts else list(cyc)
    for e in flips:
        Ne = M.nbrs(e)
        W = next((int(o[1:]) for o in opts if o[:1] == "W" and o[1:].isdigit()), 0)
        for J in range(1, 2 if "J1" in opts else K):
            gJ = -M.degree_lits(e, J)[3]
            forced = "J1" in opts or (e == e0 and J <= W)
            if forced:
                s.add_clause([gJ])  # WLOG (class symmetry, z >= 5): class J is zero-cost for e
            rguard = [] if forced else [gJ]
            V = View(M, e, J)

            def P(j, n, m, e=e, J=J):
                if j == J:
                    return True
                if j != 0:
                    return pairs.lit(j, n, m)
                # class 0 in V: C - e is a path whose ends are e's two class-0 neighbours
                if n in nbset(M, e) and m in nbset(M, e):
                    v = M.new()
                    s.add_clause([-v, x[n, 0], pairs.lit(0, n, m)])
                    s.add_clause([-v, x[m, 0], pairs.lit(0, n, m)])
                    return v
                return pairs.lit(0, n, m)
            for n in Ne:
                if n in cyc or not M.complete(n):
                    continue
                guard = [gJ, x[n, J]]
                cycle_conditions_g(V, n, J, guard, rguard)
                closure_pairs(V, n, J, guard, P)
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
            continue  # triangle positions are already excluded (Lemmas 7, 9)
        t0 = time.time()
        M = build(R, K, f, g, opts)
        tb = time.time() - t0
        ok = M.s.solve()
        print(f"K={K} R={R} {','.join(sorted(opts)) or 'base'}  {name:16s}: {'SAT' if ok else 'UNSAT'}"
              f"  vars={M.top} pairs={M.npairs} [build {tb:.0f}s, total {time.time()-t0:.0f}s]", flush=True)
        M.s.delete()
