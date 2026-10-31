"""exp31: an LLL choice of the defect set D lowers the girth threshold of Theorem B (MANUSCRIPT 3.4, problem 9.4).

Proposition 3.13 needs D (one edge on every odd cycle of F1, F2) with pairwise distance >= 5 and an option graph U
that is a pseudoforest.  Lemma 3.15: if U has a cycle, then along a geodesic Y of length lam = floor(g/2) - 1 in
that cycle there is a family S of D-edges that "spans" Y: every Y-edge (j, j+1) has r, r' in S with
pos(r) <= j < pos(r') and depth(r) + depth(r') + pos(r') - pos(r) <= 7 (depth = distance to Y, >= 1).

Choose e_C uniformly on every odd cycle C (length >= g) and apply the variable LLL with x(E) = prod beta/|C| to
  type I : two chosen edges at distance <= 4                       (726 partners per edge)
  type II: a minimal spanning family S along a non-backtracking walk Y of length lam.
Minimal families have at most one D-edge per position (the smaller depth dominates).  Weighted count per Y-step:
factor 3 for the walk, factor 2 * 3^d * t for a D-edge of depth d (t = beta/g); the two end vertices of Y allow
3^(d+1) shapes, at most a factor (3/2)^2 overall.  The 42-state transfer matrix M(t) below encodes the spanning and
the distance >= 5 conditions; mode "brute" checks it against direct enumeration on short segments (exactly, as
polynomials in t).

Condition for every variable C:  ln(beta) >= (1 + eta) * (726 * beta * t + S2),
  S2 <= (9/4) * beta * sum_{d=1..5} 12 * 3^d * sum_{k=0..lam} u_k u_{lam-k},   u_k = 1^T M(t)^k 1.
Mode cert computes u_k in decimal arithmetic with every operation rounded up (all terms are nonnegative), so its
verdict is rigorous; mode scan uses floating point.

Usage: exp31_lll_girth.py brute | scan | cert g beta_num/beta_den
"""
import itertools
import math
import sys
from fractions import Fraction

import numpy as np

INF = 99
STATES = [(l, s) for l in range(1, 7) for s in list(range(1, 7)) + [INF]]
IDX = {st: i for i, st in enumerate(STATES)}


def transitions(t):
    """Entries (to, from, weight) of M(t).  State after position j: l = min(depth + j - pos) over placed D-edges
    (capped at 6), s = budget of the pending requirement relative to j (INF = none)."""
    out = []
    for (l, s) in STATES:
        if l > 5:                                   # edge (j, j+1) cannot be spanned
            continue
        s1 = min(s, 7 - l) - 1                      # need (pos' - (j+1)) + depth' <= s1
        l1 = min(l + 1, 6)
        if s1 >= 1:
            out.append(((l1, s1), (l, s), 3))
        for d in range(1, 6):
            if l1 + d < 5:                          # distance to an earlier D-edge would be < 5
                continue
            if d <= s1:
                out.append(((min(l1, d), INF), (l, s), 3 * 2 * 3 ** d * t))
            elif s1 >= 1:
                out.append(((min(l1, d), s1), (l, s), 3 * 2 * 3 ** d * t))
    return out


def matrix(t):
    A = np.zeros((len(STATES), len(STATES)))
    for to, fr, w in transitions(t):
        A[IDX[to], IDX[fr]] += w
    return A


def rho(t):
    return max(abs(np.linalg.eigvals(matrix(t))))


def brute(n, t):
    tot = Fraction(0)
    for conf in itertools.product(range(6), repeat=n + 1):
        if conf[0] == 0:
            continue
        pts = [(p, d) for p, d in enumerate(conf) if d]
        if any(a + b + q - p < 5 for (p, a), (q, b) in itertools.combinations(pts, 2)):
            continue
        if not all(any(a + b + q - p <= 7 for (p, a) in pts if p <= j for (q, b) in pts if q > j) for j in range(n)):
            continue
        w = 3 ** n
        for _, d in pts:
            w *= 2 * 3 ** d * t
        tot += w
    return tot


def via_matrix(n, t):
    """Same count from M(t), in exact arithmetic: start with one D-edge at position 0, end with nothing pending."""
    trans = transitions(t)
    tot = Fraction(0)
    for d0 in range(1, 6):
        v = {(d0, INF): 2 * 3 ** d0 * t}
        for _ in range(n):
            w = {}
            for to, fr, wt in trans:
                if fr in v:
                    w[to] = w.get(to, 0) + wt * v[fr]
            v = w
        tot += sum(x for (l, s), x in v.items() if s == INF)
    return tot


def margin_float(g, beta):
    t = beta / g
    A = matrix(t)
    lam = g // 2 - 1
    v, logu, sc = np.ones(len(STATES)), [math.log(len(STATES))], 0.0
    for _ in range(lam):
        v = A @ v
        s = v.sum()
        sc += math.log(s)
        v /= s
        logu.append(sc)
    terms = [logu[k] + logu[lam - k] for k in range(lam + 1)]
    top = max(terms)
    conv = top + math.log(sum(math.exp(x - top) for x in terms))
    s2 = 2.25 * beta * 12 * sum(3 ** d for d in range(1, 6)) * math.exp(conv)
    eta = (beta / g) / (1 - beta / g)
    return math.log(beta) - (1 + eta) * (726 * beta * t + s2), s2


def certificate(g, beta):
    """Rigorous check of the LLL condition.  Every decimal operation on the right-hand side runs in a context with
    ROUND_CEILING (all quantities are nonnegative, so the results are upper bounds).  ln(beta) is taken of beta
    rounded down, to 50 digits (correctly rounded), and lowered by 1e-40."""
    import decimal
    up = decimal.Context(prec=50, rounding=decimal.ROUND_CEILING)
    down = decimal.Context(prec=50, rounding=decimal.ROUND_FLOOR)
    t = beta / g
    n = len(STATES)
    entries = {}
    for to, fr, w in transitions(t):
        entries[(IDX[to], IDX[fr])] = entries.get((IDX[to], IDX[fr]), Fraction(0)) + Fraction(w)
    lam = g // 2 - 1
    with decimal.localcontext(up):
        D = lambda q: decimal.Decimal(q.numerator) / decimal.Decimal(q.denominator)
        rows = [[(j, D(w)) for (i2, j), w in entries.items() if i2 == i] for i in range(n)]
        v = [decimal.Decimal(1)] * n
        u = [decimal.Decimal(n)]
        for _ in range(lam):
            v = [sum((w * v[j] for j, w in row), decimal.Decimal(0)) for row in rows]
            u.append(sum(v, decimal.Decimal(0)))
        conv = sum((u[k] * u[lam - k] for k in range(lam + 1)), decimal.Decimal(0))
        s2 = D(Fraction(9, 4) * beta * 12 * sum(3 ** d for d in range(1, 6))) * conv
        typeI = D(726 * beta * t)
        one_eta = D(1 / (1 - beta / g))             # 1 + eta = 1/(1 - x), x = beta/g
        rhs = one_eta * (typeI + s2)
    beta_down = down.divide(decimal.Decimal(beta.numerator), decimal.Decimal(beta.denominator))
    lhs = down.ln(beta_down) - decimal.Decimal("1e-40")
    return lhs, rhs, s2


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "brute":
        # both counts are polynomials in t of degree <= n + 1 <= 8, so agreement at 9 points is an identity
        ts = [Fraction(1, q) for q in (997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049)]
        for n in range(1, 8):
            same = all(brute(n, t) == via_matrix(n, t) for t in ts)
            print(f"segment of {n} edges: brute == matrix exactly at 9 rational t "
                  f"(e.g. t = 1/997: {float(brute(n, ts[0])):.9e})  {'OK' if same else 'DIFF'}")
    elif mode == "scan":
        lo, hi = 1e-7, 1e-1
        for _ in range(200):
            mid = math.sqrt(lo * hi)
            lo, hi = (mid, hi) if rho(mid) < 1 else (lo, mid)
        print(f"critical t* = {lo:.5e}  (1/t* = {1 / lo:.1f}); type II alone needs g > beta/t*")
        print(f"type I alone needs g >= min_beta 726 beta^2/ln beta = 726*2e = {726 * 2 * math.e:.0f}")
        for g in range(5600, 5801, 20):
            best = max((margin_float(g, b) + (b,) for b in np.arange(1.15, 1.30, 0.001)), key=lambda z: z[0])
            print(f"g = {g}: best beta = {best[2]:.3f}, margin ln(beta) - rhs = {best[0]:+.2e}, S2 = {best[1]:.1e}")
    elif mode == "cert":
        g = int(sys.argv[2])
        bn, bd = map(int, sys.argv[3].split("/"))
        beta = Fraction(bn, bd)
        print(f"g = {g}, beta = {float(beta)}; spectral radius of M(beta/g) = {rho(float(beta / g)):.5f}")
        lhs, rhs, s2 = certificate(g, beta)
        print(f"ln beta >= {lhs:.8f};  (1+eta)(726 beta t + S2) <= {rhs:.8f}  (S2 <= {s2:.3e}, rounded up)  "
              f"{'LLL condition holds' if lhs >= rhs else 'FAILS'}")
