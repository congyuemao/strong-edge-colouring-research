"""Experiment 9: stronger potentials for route Q in the universal local model of exp8.

Same setting as exp8: 4-regular tree ball around e0 = (0,1), e0 on an odd cycle of class 0 whose
cycle-neighbours of e0 are f, g.  On top of exp8's conditions R1-R5 (valid for any
(Phi1, Phi2)-lexicographic minimum) this script can add:

 tie-breakers   a third potential psi, i.e. the partition is lex-min for (Phi1, Phi2, psi).
                Every flip of e in {e0,f,g} into a zero-cost class j (Lemma 3) keeps Phi1 and
                Phi2, so it must not decrease psi.  With large girth the new odd cycle is the
                triangle {e,n,m} when the closure {n,m} is a K2, and long otherwise (Lemma 6).
                  spanmin / spanmax : psi = +/- sum over odd cycles of |V(G-span)|
                  k2min   / k2max   : psi = +/- number of K2 components
 chainL         WLOG classes 1..L are zero-cost for e0.  Flipping e0 into class J gives another
                (Phi1, Phi2)-lex-min (Lemma 3), whose odd cycle passes through e0 and its two
                class-J neighbours; R1, R3, R4 (and short) are imposed there in the new state.
 R1all          single-move Phi1 minimality at every complete edge (both states).

Any potential that depends only on the multiset of inside-degrees (e.g. a convex weight
sum_e h(d_own(e))) is unchanged by a flip (f,g: 2->1, x,y: 1->2, e: 2->2), so it adds no flip
condition; that family is therefore not tested here.

UNSAT at every (f,g) position would mean the corresponding minimum has no odd cycle when the
girth exceeds the model diameter."""
import itertools
import sys
import time

import exp8_local_sat as E8
from exp8_local_sat import Model, pair_types

_nb = {}


def nbrs_cached(self, e):
    key = (self.R, e)
    if key not in _nb:
        _nb[key] = Model._nbrs_raw(self, e)
    return _nb[key]


Model._nbrs_raw = Model.nbrs
Model.nbrs = nbrs_cached
_nbset = {}


def nbset(M, e):
    key = (M.R, e)
    if key not in _nbset:
        _nbset[key] = set(M.nbrs(e))
    return _nbset[key]


def span(*edges):
    return len(set(v for e in edges for v in e))


class View:
    """Another partition of the same tree ball: same solver and counter, edge `moved` recoloured."""

    def __init__(self, base, moved, cls):
        self.base, self.moved = base, moved
        self.s, self.T, self.R, self.K, self.E = base.s, base.T, base.R, base.K, base.E
        self.x = dict(base.x)
        for c in range(base.K):
            self.x[moved, c] = base.TRUE if c == cls else -base.TRUE
        self.D = {}
        self.r1 = set()

    def new(self):
        return self.base.new()

    def nbrs(self, e):
        return self.base.nbrs(e)

    def complete(self, e):
        return self.base.complete(e)

    def degree_lits(self, e, c, cap=4):
        if self.moved not in nbset(self.base, e):
            return self.base.degree_lits(e, c, cap)
        return Model.degree_lits(self, e, c, cap)


def R1(V, w):
    if w not in V.r1:
        V.r1.add(w)
        Model.R1(V, w)


def cycle_conditions(V, e, own, guard, short, use_R5):
    """e lies on an odd cycle of class `own` in partition V (whenever all `guard` literals hold)."""
    s, x, K = V.s, V.x, V.K
    neg = [-l for l in guard]
    R1(V, e)
    Ne = V.nbrs(e)
    for j in range(K):
        if j == own:
            continue
        Dj = V.degree_lits(e, j)
        if short:
            for n, m in itertools.combinations(Ne, 2):
                if m not in nbset(V.base, n):
                    s.add_clause(neg + [-x[n, j], -x[m, j], Dj[3]])
        for n in Ne:
            if not V.complete(n):
                continue
            g1 = neg + [-x[n, j], Dj[3]]
            Dn = {c: V.degree_lits(n, c) for c in range(K)}
            R1(V, n)
            s.add_clause(g1 + [-Dn[j][2]])
            s.add_clause(g1 + [Dn[j][1]])
            for k in range(K):
                if k not in (own, j):
                    s.add_clause(g1 + [Dn[k][2]])
            s.add_clause(g1 + [Dn[own][3]])
            if use_R5:
                for k in range(K):
                    if k in (own, j):
                        continue
                    for z in V.nbrs(n):
                        if not V.complete(z):
                            continue
                        Dz = V.degree_lits(z, k)
                        pre = g1 + [-Dn[k][2], Dn[k][3], -x[z, k]]
                        s.add_clause(pre + [-Dz[2]])
                        s.add_clause(pre + [Dz[1]])


def tiebreak(M, cyc, s0, mode, own=0, guard=()):
    """Flip conditions for psi; s0 = G-span of the odd cycle `cyc` if it is a triangle, else None."""
    s, x, K = M.s, M.x, M.K
    neg = [-l for l in guard]
    for e in cyc:
        Ne = M.nbrs(e)
        for j in range(K):
            if j == own:
                continue
            Dj = M.degree_lits(e, j)
            for n, m in itertools.combinations(Ne, 2):
                adj = m in nbset(M.base, n)
                s1 = span(e, n, m) if adj else None
                if mode == "spanmin":
                    bad = adj and (s0 is None or s1 < s0)
                elif mode == "spanmax":
                    bad = s0 is not None and (not adj or s1 > s0)
                elif mode == "k2min":
                    bad = s0 is None and adj
                elif mode == "k2max":
                    bad = s0 is not None and not adj
                elif mode == "typed":
                    # psi3 = phi(type) with compact > spread > long, psi4 = -#(linked K2 components)
                    if s0 is None:
                        bad = False
                    elif not adj:
                        bad = True
                    elif s0 == 4:
                        bad = s1 > 4
                    else:
                        rest = [t for t in cyc if t != e]
                        left_linked = not set(rest[0]) & set(rest[1])
                        bad = s1 == 5 and left_linked and bool(set(n) & set(m))
                else:
                    raise ValueError(mode)
                if bad:
                    s.add_clause(neg + [-x[n, j], -x[m, j], Dj[3]])


def ttype(*edges):
    return 0 if span(*edges) <= 4 else 1  # 0 = compact triangle, 1 = spread triangle


def linked(a, b):
    return not set(a) & set(b)


def flip_delta(cyc, e, n, m, adj):
    """Change of (#compact, #spread, -#linked K2) when triangle `cyc` is broken by flipping e into
    the closure {n,m} (a K2 if adj, otherwise a long even path)."""
    d = [0, 0, 0]
    d[ttype(*cyc)] -= 1
    rest = [t for t in cyc if t != e]
    d[2] -= linked(*rest)
    if adj:
        d[ttype(e, n, m)] += 1
        d[2] += linked(n, m)
    return d


def tiebreak_rel(V, cyc, off, own, guard):
    """V differs from the minimum S0 by potential offset `off`; no flip at the triangle `cyc` may
    reach a state whose potential is lexicographically below S0's."""
    s, x, K = V.s, V.x, V.K
    neg = [-l for l in guard]
    for e in cyc:
        Ne = V.nbrs(e)
        for j in range(K):
            if j == own:
                continue
            Dj = V.degree_lits(e, j)
            for n, m in itertools.combinations(Ne, 2):
                if n in cyc or m in cyc:
                    continue
                adj = m in nbset(V.base, n)
                tot = tuple(a + b for a, b in zip(off, flip_delta(cyc, e, n, m, adj)))
                if tot < (0, 0, 0):
                    s.add_clause(neg + [-x[n, j], -x[m, j], Dj[3]])


def build(R, K, f, g, opts):
    M = Model(R, K)
    M.TRUE = M.new()
    M.s.add_clause([M.TRUE])
    M.r1 = set()
    M.base = M
    e0 = (0, 1)
    s, x = M.s, M.x
    short, use_R5 = "short" in opts, "R5" in opts
    N0 = M.nbrs(e0)
    for e in (e0, f, g):
        s.add_clause([x[e, 0]])
    for n in N0:
        if n not in (f, g):
            s.add_clause([-x[n, 0]])
    for e in (e0, f, g):
        D0 = M.degree_lits(e, 0)
        s.add_clause([D0[2]])
        s.add_clause([-D0[3]])
    for e in (e0, f, g):
        cycle_conditions(M, e, 0, [], short, use_R5)
    if "R1all" in opts:
        for w in M.E:
            if M.complete(w):
                R1(M, w)
    s0 = span(e0, f, g) if g in nbset(M, f) else None
    for mode in ("spanmin", "spanmax", "k2min", "k2max", "typed"):
        if mode in opts:
            tiebreak(M, (e0, f, g), s0, mode)
    if "rel" in opts and s0 is not None:
        tiebreak_rel(M, (e0, f, g), (0, 0, 0), 0, [])
    if "chainall" in opts and s0 is not None:
        # flip e0 into every zero-cost class J and every K2 closure {n,m}; the resulting state S1
        # must not allow a further flip that lands below S0
        for J in range(1, K):
            gJ = -M.degree_lits(e0, J)[3]
            V = View(M, e0, J)
            for n, m in itertools.combinations(N0, 2):
                if n in (f, g) or m in (f, g) or m not in nbset(M, n):
                    continue
                off = tuple(flip_delta((e0, f, g), e0, n, m, True))
                if off < (0, 0, 0):
                    continue
                tiebreak_rel(V, (e0, n, m), off, J, [gJ, x[n, J], x[m, J]])
                # V is a Phi1 minimum only when the flip is zero-cost, so R1 is guarded by gJ
                # (an unguarded R1 here over-constrains; fixed 2026-10-30, see ROUTE_Q_zh.md 9.2)
                from exp11_pairing import R1g
                R1g(V, n, [gJ])
                R1g(V, m, [gJ])
    L = next((int(o[5:]) for o in opts if o.startswith("chain") and o[5:].isdigit()), 0)
    for J in range(1, L + 1):
        s.add_clause([-M.degree_lits(e0, J)[3]])  # WLOG: class J is zero-cost for e0
        V = View(M, e0, J)
        for n in N0:
            # in V, n's class-J neighbours are on the new odd cycle through e0
            cycle_conditions(V, n, J, [x[n, J]], short, False)
        if "typed" in opts and s0 == 5:
            # a psi-neutral flip (spread -> spread, same K2 type left and consumed) gives another
            # minimum of the full potential, so the typed conditions hold at the new triangle too
            left_linked = not set(f) & set(g)
            for n, m in itertools.combinations(N0, 2):
                if m in nbset(M, n) and span(e0, n, m) == 5 and (not set(n) & set(m)) == left_linked:
                    tiebreak(V, (e0, n, m), 5, "typed", own=J, guard=[x[n, J], x[m, J]])
        if "R1all" in opts:
            for w in M.E:
                if M.complete(w) and e0 in nbset(M, w) | {w}:
                    R1(V, w)
    return M


if __name__ == "__main__":
    K = int(sys.argv[1])
    R = int(sys.argv[2])
    opts = set(sys.argv[3].split(",")) if len(sys.argv) > 3 else set()
    only = sys.argv[4].split(";") if len(sys.argv) > 4 else None
    for name, (f, g) in pair_types().items():
        if only and name not in only:
            continue
        t0 = time.time()
        M = build(R, K, f, g, opts)
        ok = M.s.solve()
        tri = "triangle" if g in nbset(M, f) else "long"
        print(f"K={K} R={R} {','.join(sorted(opts)) or 'base'}  {name:16s} ({tri:8s} span={span((0, 1), f, g) if tri == 'triangle' else '-'}): "
              f"{'SAT' if ok else 'UNSAT'}  vars={M.top} [{time.time()-t0:.1f}s]", flush=True)
        M.s.delete()
