"""Direct check that spread triangles cannot occur (the counting behind Lemma 9).

Potential: lex-min of (Phi1, Phi2, #compact, #spread, -#linked K2), girth >= 7 (tree model).
For a spread triangle T = {e0,f,g} of class 0 and each e in T:
  1. list e's admissible closures in S0 (K2 pairs {x,y} whose flip does not go below S0);
  2. for each, flip e into it (state S1, potential offset `off` from S0) and, at every edge e' of the
     new triangle T1, bound the number of admissible closures in S1 (flips must not go below S0):
     closures lie in distinct classes, and T \\ {e} is the K2 left in class 0, so at most one
     closure may use those two edges;
  3. a closure survives only if every e' in T1 still has >= 5;
  4. e needs >= 5 pairwise disjoint surviving closures (Lemma 2)."""
import itertools

import networkx as nx

from exp8_local_sat import Model, pair_types
from exp9_potentials import flip_delta

M = Model(5, 2)
nb = {e: set(M.nbrs(e)) for e in M.E}


def admissible(cyc, off, e, banned):
    out = []
    for x, y in itertools.combinations(sorted(nb[e] - set(cyc) - banned), 2):
        if y in nb[x] and tuple(a + b for a, b in zip(off, flip_delta(cyc, e, x, y, True))) >= (0, 0, 0):
            out.append((x, y))
    return out


def max_closures(pairs, zero):
    """Max # disjoint pairs, at most one of which meets the class-0 set `zero`."""
    H = nx.Graph(p for p in pairs if not set(p) & zero)
    best = len(nx.max_weight_matching(H, maxcardinality=True))
    for p in pairs:
        if set(p) & zero:
            H2 = H.copy()
            H2.remove_nodes_from(p)
            best = max(best, 1 + len(nx.max_weight_matching(H2, maxcardinality=True)))
    return best


for name, (f, g) in pair_types().items():
    T = ((0, 1), f, g)
    if g not in nb[f] or len(set(v for e in T for v in e)) != 5:
        continue
    print(f"== spread position {name}")
    for e in T:
        rest = set(t for t in T if t != e)
        S0 = admissible(T, (0, 0, 0), e, set())
        surv = []
        for x, y in S0:
            off = tuple(flip_delta(T, e, x, y, True))
            T1 = (e, x, y)
            worst = min(max_closures(admissible(T1, off, ep, set()), rest) for ep in T1)
            if worst >= 5:
                surv.append((x, y))
        H = nx.Graph(surv)
        k = len(nx.max_weight_matching(H, maxcardinality=True))
        print(f"   edge {e}: {len(S0)} admissible closures in S0, {len(surv)} survive the S1 test, "
              f"max disjoint = {k}  -> {'IMPOSSIBLE' if k < 5 else 'possible'}")
