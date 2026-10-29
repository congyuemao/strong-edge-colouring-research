"""Experiment 13: Brooks-type partitions -- a route to 20 colours whose obstructions are all local.

Split E(G) into k classes with degree bounds d_1..d_k in L^2 (the conflict graph), sum d_i = 20.
  Lovasz:  a minimiser of Psi = sum_i (e(V_i) - d_i |V_i|) has Delta(L^2[V_i]) <= d_i as soon as
           sum (d_i + 1) >= 25  (moving w from i to j changes Psi by (deg_j - deg_i) + (d_i - d_j)).
  Brooks:  for d_i >= 3, L^2[V_i] is d_i-colourable unless a component is K_{d_i+1} ("bad").
           d_i = 1: the class must be independent; bad = K2.  (d_i = 2 would need bipartite,
           a global condition -- that is route Q, = d = (2^10).)
So chi'_s <= 20 follows once some (Psi, #bad)-lex-minimum has no bad component.  A bad
component is a clique, i.e. a LOCAL object, unlike route Q's long odd cycles.

Every edge w of a 4-regular graph of girth >= 5 has 24 conflicts, so the excesses
eps_j(w) = deg_j(w) - d_j satisfy sum_j eps_j(w) = 24 - 20 = 4, and Psi-minimality says that the
own excess is the minimum one.  For w in a bad clique the own excess is 0, so w has >= k - 5
"tight" classes j (eps_j = 0); moving w there keeps Psi, destroys the clique, and so must create
a new bad clique: w's d_j neighbours in V_j are a clique forming a K_{d_j} component.

Local model (4-regular tree ball around e0 = (0,1), i.e. girth larger than the ball):
  S0       a Psi-minimum (single moves, every complete edge) with bad clique X in class 0;
  kill     for x in X and each class j:  tight_j(x) -> N_j(x) is a clique and each of its
           members has deg_j <= d_j - 1 (max degree in the new state);
  level 1  in S1 = S0 + (x -> j) (again a lex-minimum when tight) the new bad clique is
           {x} + N_j(x); Psi-minimality near x and the kill conditions of its members.
UNSAT for a clique type = that type of bad clique cannot occur in a lex-minimum."""
import itertools
import sys
import time

import exp9_potentials  # noqa: F401  (caches Model.nbrs)
from exp8_local_sat import Model
from exp9_potentials import nbset


class State:
    """The base partition with some edges moved to fixed classes; shares the solver."""

    def __init__(self, M, moves):
        self.M, self.moves = M, dict(moves)
        self.s, self.T, self.R, self.K = M.s, M.T, M.R, M.K
        self.x = dict(M.x)
        for e, c in moves.items():
            for k in range(M.K):
                self.x[e, k] = M.TRUE if k == c else -M.TRUE
        self.D = {}

    def new(self):
        return self.M.new()

    def nbrs(self, e):
        return self.M.nbrs(e)

    def complete(self, e):
        return self.M.complete(e)

    def ge(self, e, c, k):
        """Literal: (#conflicts of e in class c) >= k."""
        M = self.M
        if k <= 0:
            return M.TRUE
        if k > M.cap:
            return -M.TRUE
        if not any(m in nbset(M, e) for m in self.moves):
            return M.degree_lits(e, c, M.cap)[k]
        if (e, c) not in self.D:
            Model.degree_lits(self, e, c, M.cap)
        return self.D[e, c][k]


def card(M, lits, cap):
    """ge[k] <-> (#true among lits) >= k, k = 1..cap (sequential counter, both directions)."""
    s = M.s
    prev = {}
    for i, l in enumerate(lits):
        cur = {}
        for k in range(1, min(cap, i + 1) + 1):
            v = M.new()
            cur[k] = v
            a = prev.get(k)
            b = prev.get(k - 1) if k > 1 else M.TRUE
            if a is not None:
                s.add_clause([-a, v])
            s.add_clause([-b, -l, v])
            s.add_clause([-v, b] + ([a] if a is not None else []))
            s.add_clause([-v, l] + ([a] if a is not None else []))
        prev = cur
    return {k: prev.get(k, -M.TRUE) for k in range(1, cap + 1)}


def at_ends(M, w):
    """The 6 edges sharing an endpoint with w (tiebreak T only looks at these)."""
    return [y for y in M.nbrs(w) if set(y) & set(w)]


def dT(S, w, p, j):
    """Move w: p -> j changes T = sum_u sum_c C(n_c(u), 2) by (#j) - (#p) over at_ends(w)."""
    ends = at_ends(S.M, w)
    return [S.x[y, j] for y in ends], [S.x[y, p] for y in ends]


def require_nonneg(S, guard, acc):
    """guard -> sum(pos) - sum(neg) >= 0 over the accumulated moves acc = (pos, neg)."""
    pos, neg = acc
    if not neg:
        return
    c = card(S.M, pos + [-l for l in neg], len(neg))
    S.s.add_clause([-l for l in guard] + [c[len(neg)]])


def psi_min(S, d, y, guard):
    """Single-move Psi-minimality at y:  eps_own(y) <= eps_j(y) for all j."""
    neg = [-l for l in guard]
    x = S.x
    for i in range(S.K):
        S.s.add_clause(neg + [-x[y, i], -S.ge(y, i, d[i] + 1)])
        for j in range(S.K):
            if j == i:
                continue
            for a in range(0, d[i] + 1):
                need = a - d[i] + d[j]
                if need >= 1:
                    S.s.add_clause(neg + [-x[y, i], -S.ge(y, i, a), S.ge(y, j, need)])


def kill(S, d, w, p, guard, level, stats, acc=None):
    """w lies in a bad clique of class p in state S (whenever all `guard` hold)."""
    M, x = S.M, S.x
    neg = [-l for l in guard]
    Nw = S.nbrs(w)
    # hint (implied by sum_j eps_j = 4, eps_p = 0): at most 4 units of visible excess
    units = [S.ge(w, j, d[j] + r) for j in range(S.K) if j != p
             for r in range(1, S.M.cap - d[j] + 1)]
    c = card(M, units, 5)
    S.s.add_clause(neg + [-c[5]])
    for j in range(S.K):
        if j == p:
            continue
        t = -S.ge(w, j, d[j] + 1)      # tight: deg_j(w) = d_j (>= d_j by psi_min)
        for y, z in itertools.combinations(Nw, 2):
            if z not in nbset(M, y):
                S.s.add_clause(neg + [-t, -x[y, j], -x[z, j]])
        for y in Nw:
            if S.complete(y):
                S.s.add_clause(neg + [-t, -x[y, j], -S.ge(y, j, d[j])])
        if acc is not None:
            dpos, dneg = dT(S, w, p, j)
            acc1 = (acc[0] + dpos, acc[1] + dneg)
            require_nonneg(S, guard + [t], acc1)
        if "B" in S.M.opts:
            two_step(S, d, w, p, j, guard + [t], acc)
        if level == 0:
            continue
        mv = dict(S.moves)
        mv[w] = j
        S1 = State(M, mv)
        stats["states"] += 1
        g1 = guard + [t]
        for y in [w] + Nw:
            if S1.complete(y):
                psi_min(S1, d, y, g1)
        for y in Nw:
            if S1.complete(y) and y not in S.moves:
                kill(S1, d, y, j, g1 + [x[y, j]], level - 1, stats,
                     None if acc is None else acc1)


def two_step(S, d, w, p, j, guard, acc):
    """Lemma B.  w in a bad clique of class p, j tight for w, q in N_j(w).  Moving q to m and then
    w to j changes Psi by eps_m(q) and destroys w's clique, so for every m not in {j, p}:
    eps_m(q) >= 0, and eps_m(q) = 0 forces q to complete a bad clique in m (and, with T, the
    two moves together must not decrease T)."""
    M, x = S.M, S.x
    for q in S.nbrs(w):
        if not S.complete(q) or q in S.moves:
            continue
        g = guard + [x[q, j]]
        neg = [-l for l in g]
        Nq = S.nbrs(q)
        for m in range(S.K):
            if m in (j, p):
                continue
            S.s.add_clause(neg + [S.ge(q, m, d[m])])
            t = -S.ge(q, m, d[m] + 1)           # eps_m(q) = 0
            for y, z in itertools.combinations(Nq, 2):
                if z not in nbset(M, y):
                    S.s.add_clause(neg + [-t, -x[y, m], -x[z, m]])
            for y in Nq:
                if S.complete(y):
                    S.s.add_clause(neg + [-t, -x[y, m], -S.ge(y, m, d[m])])
            if acc is not None:
                mv = dict(S.moves)
                mv[q] = m
                S2 = State(M, mv)
                p1, n1 = dT(S, q, j, m)
                p2, n2 = dT(S2, w, p, j)
                require_nonneg(S, g + [t], (acc[0] + p1 + p2, acc[1] + n1 + n2))


def t_min_all(M, d):
    """Every zero-cost move y: i -> m that creates no bad clique must not decrease T."""
    x, K = M.x, M.K
    cnt = {}
    for y in M.E:
        if not M.complete(y):
            continue
        ends = at_ends(M, y)
        for c in range(K):
            cnt[c] = card(M, [x[z, c] for z in ends], 6)
        for i in range(K):
            for m in range(K):
                if m == i:
                    continue
                # cb: moving y creates a bad clique (needs own-degree d_i and N_m(y) a K_{d_m})
                cb = M.new()
                M.s.add_clause([-cb, M.degree_lits(y, i, M.cap)[d[i]]])
                M.s.add_clause([-cb, -M.degree_lits(y, m, M.cap)[d[m] + 1]])
                for y1, y2 in itertools.combinations(M.nbrs(y), 2):
                    if y2 not in nbset(M, y1):
                        M.s.add_clause([-cb, -x[y1, m], -x[y2, m]])
                for a in range(0, d[i] + 1):
                    up = a - d[i] + d[m]          # zero-cost iff deg_m(y) <= up
                    if up < 0:
                        continue
                    zc = [-x[y, i], -ge(M, y, i, a), ge(M, y, i, a + 1), ge(M, y, m, up + 1)]
                    for r in range(1, 7):         # #i >= r and #m <= r-1  ->  cb
                        M.s.add_clause(zc + [-cnt[i][r], cnt[m][r], cb])


def ge(M, e, c, k):
    if k <= 0:
        return M.TRUE
    if k > M.cap:
        return -M.TRUE
    return M.degree_lits(e, c, M.cap)[k]


def clique_types():
    T = Model(2, 1).T
    a = sorted(v for v in T[0] if v != 1)
    b = sorted(v for v in T[1] if v != 0)
    e0 = (0, 1)
    A = [(0, v) for v in a]
    B = [(1, v) for v in b]
    return {
        4: {"S(u)": [e0] + A, "e+2+1": [e0, A[0], A[1], B[0]],
            "3+1": A + [B[0]], "2+2": [A[0], A[1], B[0], B[1]]},
        5: {"S(u)+1": [e0] + A + [B[0]], "e+2+2": [e0, A[0], A[1], B[0], B[1]],
            "3+2": A + [B[0], B[1]]},
        2: {"K2-hub": [e0, A[0]], "K2-far": [A[0], B[0]]},
        6: {"S(u)+2": [e0] + A + B[:2], "e+3+2 no": A + B, "e+2+3": [e0] + A[:2] + B},
    }


def build(R, d, X, level, opts=()):
    K = len(d)
    M = Model(R, K)
    M.opts = set(opts)
    M.cap = max(d) + 1
    M.TRUE = M.new()
    M.s.add_clause([M.TRUE])
    S0 = State(M, {})
    S0.x = M.x
    S0.D = M.D
    x = M.x
    for w in X:
        M.s.add_clause([x[w, 0]])
        for y in M.nbrs(w):
            if y not in X:
                M.s.add_clause([-x[y, 0]])
    for y in M.E:
        if M.complete(y):
            psi_min(S0, d, y, [])
    if "Tall" in opts:
        t_min_all(M, d)
    stats = {"states": 0}
    for w in X:
        kill(S0, d, w, 0, [], level, stats, ([], []) if "T" in opts else None)
    M.nstates = stats["states"]
    return M


if __name__ == "__main__":
    d = [int(c) for c in sys.argv[1].split(",")]
    R = int(sys.argv[2])
    level = int(sys.argv[3])
    opts = set(sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    only = sys.argv[5].split(";") if len(sys.argv) > 5 else None
    assert sum(d) == 20 and sum(c + 1 for c in d) >= 25
    for name, X in clique_types()[d[0] + 1].items():
        if only and name not in only:
            continue
        t0 = time.time()
        M = build(R, d, X, level, opts)
        tb = time.time() - t0
        ok = M.s.solve()
        print(f"d={d} R={R} level={level} {','.join(sorted(opts)) or 'base'}  bad {name:7s}: {'SAT' if ok else 'UNSAT'}"
              f"  vars={M.top} states={M.nstates} [build {tb:.0f}s, total {time.time()-t0:.0f}s]",
              flush=True)
        M.s.delete()
