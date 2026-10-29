"""Experiment 14: periodic stuck paths -- which of the three cases (ROUTE_Q_zh.md, reply on LP)?

Any argument that only looks at bounded neighbourhoods of the odd cycle C (local SAT, LP over local
types, discharging along C) sees C as a bi-infinite path: parity is invisible locally.  So test
whether the stuck conditions can be laid along a bi-infinite class-0 path in the 4-regular tree
with labels invariant under the shift by L cycle positions:
  no period works          -> case (a): a density argument (LP / discharging) can succeed;
  only even periods work   -> case (b): a genuine parity proof;
  some odd period works    -> case (c): no argument local to C can exclude long odd cycles.

Tree: spine vertices (k, ()), k in Z, each with two branches (k, (0,)), (k, (1,)), every branch
vertex having 3 children.  Cycle shapes (one per long position of exp8):
  J   T(a),T(b)    cycle edges (2i, 2i+1) on the spine, joined by spine edges
  P   T(a1),T(a2)  pendant cycle edges ((k,()), (k,(0,))) at every spine vertex
  SJ  S(u),T(b)    spine edges (3m,3m+1), (3m+1,3m+2), joined by (3m+2,3m+3)  (even L only)
Conditions (all valid at a lex-min of exp9's potential, girth >= 7):
  base  R1 near the spine; e in C has class-0 degree 2 (its cycle neighbours); R3/R4 at every
        zero-cost closure of every cycle edge; no class contains an L^2-triangle (Lemmas 7, 9)
  L11   Lemma 11 depth 1: closure-path interiors satisfy R3/R4 too
  flip  e flipped into each zero-cost class J: the new odd cycle through e's J-neighbours
        satisfies R1/R3/R4 in the flipped state (exp11 without pair variables)."""
import sys
import time

from pysat.solvers import Cadical153

import exp9_potentials  # noqa: F401
from exp8_local_sat import Model
from exp9_potentials import nbset
from exp11_pairing import R1g, cycle_conditions_g
from exp12_closure_tree import interior_links

# name: (spine units per unit, cycle edges per unit, unit cycle edges)
PATTERNS = {
    "J": (2, 1, [((0, ()), (1, ()))]),
    "P": (1, 1, [((0, ()), (0, (0,)))]),
    "SJ": (3, 2, [((0, ()), (1, ())), ((1, ()), (2, ()))]),
}


def vnbrs(v, D):
    k, t = v
    out = []
    if not t:
        out += [(k - 1, ()), (k + 1, ())]
        kids = (0, 1)
    else:
        out.append((k, t[:-1]))
        kids = (0, 1, 2)
    if len(t) < D:
        out += [(k, t + (b,)) for b in kids]
    return out


def shifted(e, s):
    return tuple((v[0] + s, v[1]) for v in e)


class XMap:
    def __init__(self, M, over):
        self.M, self.over = M, over

    def __getitem__(self, key):
        e, c = key
        if e in self.over:
            return self.M.TRUE if self.over[e] == c else -self.M.TRUE
        return self.M.var(e, c)


class PModel:
    def __init__(self, pattern, L, D, K):
        u, m, unit = PATTERNS[pattern]
        assert L % m == 0
        self.u, self.unit = u, set(unit)
        self.shift = u * L // m
        self.Dmax, self.K = D, K
        self.R = ("per", pattern, L, D)
        self.s = Cadical153()
        self.top = 0
        self.TRUE = self.new()
        self.s.add_clause([self.TRUE])
        self.vars = {}
        self.x = XMap(self, {})
        self.D = {}
        self.r1 = set()

    def new(self):
        self.top += 1
        return self.top

    def rep(self, e, per):
        m0 = min(v[0] for v in e)
        return shifted(e, -(m0 // per) * per)

    def var(self, e, c):
        r = self.rep(e, self.shift)
        if (r, 0) not in self.vars:
            lits = [self.new() for _ in range(self.K)]
            for cc, l in enumerate(lits):
                self.vars[r, cc] = l
            self.s.add_clause(lits)
            for i in range(self.K):
                for j in range(i + 1, self.K):
                    self.s.add_clause([-lits[i], -lits[j]])
        return self.vars[r, c]

    def in_cycle(self, e):
        return self.rep(e, self.u) in self.unit

    def edepth(self, e):
        return max(len(v[1]) for v in e)

    def complete(self, e):
        return self.edepth(e) <= self.Dmax - 2

    def nbrs(self, e):
        a, b = e
        near = {a, b} | set(vnbrs(a, self.Dmax)) | set(vnbrs(b, self.Dmax))
        out = set()
        for w in near:
            for z in vnbrs(w, self.Dmax):
                f = tuple(sorted((w, z)))
                if f != e:
                    out.add(f)
        return sorted(out)

    def degree_lits(self, e, c, cap=4):
        return Model.degree_lits(self, e, c, cap)

    def base_edges(self, maxdepth):
        """Representatives of the edge orbits (min spine index in [0, shift))."""
        out = []
        for k in range(self.shift):
            out.append(((k, ()), (k + 1, ())))
            stack = [(k, ())]
            while stack:
                v = stack.pop()
                for w in vnbrs(v, self.Dmax):
                    if w[0] == k and len(w[1]) == len(v[1]) + 1 and len(w[1]) <= maxdepth:
                        out.append((v, w))
                        stack.append(w)
        return out


class PState:
    """The periodic partition with some single tree edges moved (their translates are not)."""

    def __init__(self, M, over):
        self.base, self.over = M, dict(over)
        self.s, self.K, self.R, self.TRUE = M.s, M.K, M.R, M.TRUE
        self.x = XMap(M, self.over)
        self.D = {}
        self.r1 = set()

    def new(self):
        return self.base.new()

    def nbrs(self, e):
        return self.base.nbrs(e)

    def complete(self, e):
        return self.base.complete(e)

    def degree_lits(self, e, c, cap=4):
        if not any(m in nbset(self.base, e) for m in self.over):
            return self.base.degree_lits(e, c, cap)
        return Model.degree_lits(self, e, c, cap)


def build(pattern, L, D, K, opts):
    M = PModel(pattern, L, D, K)
    s, x = M.s, M.x
    cyc = [e for e in M.base_edges(1) if M.in_cycle(e)]
    assert len(cyc) == L, (pattern, L, cyc)
    for e in cyc:
        s.add_clause([x[e, 0]])
        cn = [n for n in M.nbrs(e) if M.in_cycle(n)]
        assert len(cn) == 2, (e, cn)
        for n in M.nbrs(e):
            if not M.in_cycle(n):
                s.add_clause([-x[n, 0]])
    r1depth = 3
    for y in M.base_edges(r1depth):
        R1g(M, y, [])
    for a in M.base_edges(M.Dmax - 2):
        Na = M.nbrs(a)
        for b in Na:
            if b <= a:
                continue
            for c in nbset(M, b):
                if c > b and c in nbset(M, a):
                    for k in range(K):
                        s.add_clause([-x[a, k], -x[b, k], -x[c, k]])
    for e in cyc:
        cycle_conditions_g(M, e, 0, [], [])
    if "L11" in opts:
        links = {}
        for e in cyc:
            for j, p, cond in interior_links(M, M.TRUE, e, 0, ()):
                key = (M.rep(p, M.shift), j)
                if key not in links:
                    links[key] = (p, M.new())
                s.add_clause([-c for c in cond] + [links[key][1]])
        for (_, j), (p, lit) in links.items():
            cycle_conditions_g(M, p, j, [lit], [])
    if "flip" in opts:
        for e in cyc:
            for J in range(1, K):
                gJ = -M.degree_lits(e, J)[3]
                V = PState(M, {e: J})
                for n in M.nbrs(e):
                    if M.in_cycle(n) or not M.complete(n):
                        continue
                    cycle_conditions_g(V, n, J, [gJ, x[n, J]], [gJ])
    return M


if __name__ == "__main__":
    pattern = sys.argv[1]
    Ls = [int(v) for v in sys.argv[2].split(",")]
    D = int(sys.argv[3])
    opts = set(sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    K = 10
    for L in Ls:
        t0 = time.time()
        M = build(pattern, L, D, K, opts)
        tb = time.time() - t0
        ok = M.s.solve()
        print(f"pattern={pattern:2s} L={L} D={D} {','.join(sorted(opts)) or 'base'}: "
              f"{'SAT' if ok else 'UNSAT'}  vars={M.top} [build {tb:.0f}s, total {time.time()-t0:.0f}s]",
              flush=True)
        M.s.delete()
