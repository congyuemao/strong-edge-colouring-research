"""Regression test for the M1 finishing criteria (ROUTE_Q_zh.md section 13.6).

Three notions about the uncoloured residual of the nibble must not be confused:
  (1) the slack certificate fails:  some uncoloured e has |L(e)| <= u(e)  (exp16 "fail");
  (2) the fixed greedy strategy fails:  greedy_finish returns False;
  (3) the residual is uncolourable:  no colouring of the uncoloured edges from their lists.
Only the one-way implications hold:
  certificate holds  =>  every greedy order succeeds  =>  greedy_finish succeeds  =>  colourable.
The cases below show that each converse fails, starting with the Codex counterexample.
By contrast, "SOME first-fit order succeeds" is equivalent to colourability (third Codex review):
process the edges of a valid colouring c in nondecreasing order of c; each edge e gets a colour
<= c(e), so c(e) is never blocked.  Only the fixed strategy greedy_finish is strictly stronger.

Run from this directory:  python test_exp16_criteria.py   (pytest also collects it).
"""
import itertools
import random
import sys

import numpy as np

from exp16_nibble import certificate_fails, greedy_finish


def instance(k, lists, conflicts):
    """Residual instance: every edge uncoloured with the given lists.

    NB rows are padded with a sentinel edge (index m) that is already coloured and has an empty
    list, so it never counts as an uncoloured conflict and never needs a colour."""
    m = len(lists)
    nbrs = [[] for _ in range(m)]
    for a, b in conflicts:
        nbrs[a].append(b); nbrs[b].append(a)
    width = max(1, max(len(r) for r in nbrs))
    NB = np.full((m + 1, width), m, dtype=np.int32)
    for i, r in enumerate(nbrs):
        NB[i, :len(r)] = r
    col = np.full(m + 1, -1, dtype=np.int32); col[m] = 0
    avail = np.zeros((m + 1, k), dtype=bool)
    for i, L in enumerate(lists):
        avail[i, sorted(L)] = True
    return NB, col, avail, nbrs


def first_fit_in_order(nbrs, lists, order):
    """Greedy in a fixed order, each edge taking its smallest free colour."""
    c = {}
    for e in order:
        free = sorted(set(lists[e]) - {c[f] for f in nbrs[e] if f in c})
        if not free:
            return False
        c[e] = free[0]
    return True


def colourable(nbrs, lists):
    """Exact list colouring by backtracking (small instances only)."""
    m = len(lists); c = {}

    def go():
        left = [e for e in range(m) if e not in c]
        if not left:
            return True
        e = min(left, key=lambda i: len(set(lists[i]) - {c[f] for f in nbrs[i] if f in c}))
        for x in sorted(set(lists[e]) - {c[f] for f in nbrs[e] if f in c}):
            c[e] = x
            if go():
                return True
            del c[e]
        return False

    return go()


def classify(k, lists, conflicts):
    NB, col, avail, nbrs = instance(k, lists, conflicts)
    cert_fail = bool(certificate_fails(NB, col, avail).any())
    ok, _ = greedy_finish(NB, col, avail)
    orders = [first_fit_in_order(nbrs, lists, o) for o in itertools.permutations(range(len(lists)))]
    return {"certificate_fails": cert_fail, "greedy_finish_ok": bool(ok),
            "all_orders_ok": all(orders), "some_order_ok": any(orders),
            "colourable": colourable(nbrs, lists)}


def test_codex_counterexample():
    """Two conflicting edges, lists {0} and {1}: |L| = u = 1 at both, yet every order succeeds."""
    r = classify(2, [{0}, {1}], [(0, 1)])
    assert r == {"certificate_fails": True, "greedy_finish_ok": True, "all_orders_ok": True,
                 "some_order_ok": True, "colourable": True}, r


def test_greedy_strategy_fails_but_colourable():
    """Triangle with lists {0,1}, {0,2}, {0,2}: greedy_finish picks 0 for the first edge and gets
    stuck, but the colouring 1, 0, 2 exists.  A failing strategy is not an uncolourable residual."""
    r = classify(3, [{0, 1}, {0, 2}, {0, 2}], [(0, 1), (0, 2), (1, 2)])
    assert r == {"certificate_fails": True, "greedy_finish_ok": False, "all_orders_ok": False,
                 "some_order_ok": True, "colourable": True}, r


def test_truly_uncolourable():
    """Two conflicting edges that both have list {0}: every notion of failure holds."""
    r = classify(1, [{0}, {0}], [(0, 1)])
    assert r == {"certificate_fails": True, "greedy_finish_ok": False, "all_orders_ok": False,
                 "some_order_ok": False, "colourable": False}, r


def test_greedy_finish_succeeds_but_not_every_order():
    """Triangle with lists {0,2}, {0,2}, {0,1}: greedy_finish starts with edge 0 and succeeds, but
    the order 2, 0, 1 gives edge 2 colour 0 and then edges 0 and 1 both need colour 2."""
    r = classify(3, [{0, 2}, {0, 2}, {0, 1}], [(0, 1), (0, 2), (1, 2)])
    assert r == {"certificate_fails": True, "greedy_finish_ok": True, "all_orders_ok": False,
                 "some_order_ok": True, "colourable": True}, r


def test_certificate_holds_every_order_succeeds():
    """Lists larger than the number of uncoloured conflicts: the certificate holds."""
    r = classify(3, [{0, 1}, {1, 2}], [(0, 1)])
    assert r == {"certificate_fails": False, "greedy_finish_ok": True, "all_orders_ok": True,
                 "some_order_ok": True, "colourable": True}, r


def test_random_implications_and_strictness(trials=3000, seed=20261030):
    """On random small residuals the forward implications always hold, each converse fails, and
    'some order succeeds' coincides with colourability."""
    rng = random.Random(seed)
    strict = {"cert_fails_but_all_orders_ok": 0, "greedy_ok_but_not_all_orders": 0,
              "greedy_fails_but_colourable": 0}
    for _ in range(trials):
        m = rng.randint(2, 6); k = rng.randint(1, 4)
        conflicts = [(a, b) for a in range(m) for b in range(a + 1, m) if rng.random() < 0.5]
        lists = [set(rng.sample(range(k), rng.randint(1, k))) for _ in range(m)]
        r = classify(k, lists, conflicts)
        if not r["certificate_fails"]:
            assert r["all_orders_ok"] and r["greedy_finish_ok"], (lists, conflicts, r)
        if r["greedy_finish_ok"] or r["some_order_ok"]:
            assert r["colourable"], (lists, conflicts, r)
        if r["all_orders_ok"]:
            assert r["greedy_finish_ok"], (lists, conflicts, r)
        assert r["some_order_ok"] == r["colourable"], (lists, conflicts, r)
        strict["cert_fails_but_all_orders_ok"] += r["certificate_fails"] and r["all_orders_ok"]
        strict["greedy_ok_but_not_all_orders"] += r["greedy_finish_ok"] and not r["all_orders_ok"]
        strict["greedy_fails_but_colourable"] += (not r["greedy_finish_ok"]) and r["colourable"]
    assert all(v > 0 for v in strict.values()), strict
    return strict


if __name__ == "__main__":
    failed = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                out = fn()
                print(f"PASS {name}" + (f"  {out}" if out else ""))
            except AssertionError as exc:
                failed += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failed else 0)
