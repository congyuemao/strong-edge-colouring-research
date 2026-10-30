"""exp19: property M -- the matching-contraction framework on small and medium-girth graphs.

Property M_t (budget B): E(G) splits into at most t matchings M_1..M_t with
  sum_i chi(H(M_i)) <= B,   H(M) = conflict graph inside the matching M (= G/M).
Equivalently: a strong B-colouring together with a map colour -> group (t groups) such that
the edges of each group form a matching.  Without the cap t the property is trivial (split into
the strong colour classes), so the cap is what gives it content.
  M4 (B=20): the class-1 form used by Theorem A (4 matchings x 5 colours).
  M5 (B=20): the general form used by Theorem B (5 + 5 + 5 + 4 + 1).

Modes
  small N       all connected quartic graphs on 5..N vertices (graphs_n*.txt): M4, then M5 if M4 fails
  tight N       the same graphs: does M_t (t = chi'(G)) already hold with 19, and with 18, colours?
  exact Ns      even n in the comma list Ns: exact least budget for M4 over all 1-factorisations
  slack n g s   random graphs, max degree 4, girth >= g, s seeds: chromatic numbers of H(M_i) for a
                SAT 4-edge-colouring, and whether M4 already holds with 16 colours
"""
import itertools
import multiprocessing as mp
import sys
import time

from pysat.solvers import Cadical153


def load(n):
    with open(f"graphs_n{n}.txt") as fh:
        for line in fh:
            yield [tuple(map(int, t.split("-"))) for t in line.split()]


def structure(edges):
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    E = [tuple(sorted(e)) for e in edges]
    share, conf = [], []
    for i, j in itertools.combinations(range(len(E)), 2):
        a, b = set(E[i]), set(E[j])
        if a & b:
            share.append((i, j)); conf.append((i, j))
        elif any(y in adj[x] for x in a for y in b):
            conf.append((i, j))
    return E, adj, share, conf


def property_m(edges, t, B, budget=None):
    """SAT test of property M_t with B colours.  Returns True, False or None (budget hit)."""
    E, adj, share, conf = structure(edges)
    m = len(E)
    y = lambda e, k: 1 + e * B + k                     # edge e has colour k
    z = lambda e, g: 1 + m * B + e * t + g             # edge e is in group g
    w = lambda k, g: 1 + m * B + m * t + k * t + g     # colour k belongs to group g
    s = Cadical153()
    for e in range(m):
        s.add_clause([y(e, k) for k in range(B)])
        s.add_clause([z(e, g) for g in range(t)])
        for g, h in itertools.combinations(range(t), 2):
            s.add_clause([-z(e, g), -z(e, h)])
        for k in range(B):
            for g in range(t):
                s.add_clause([-y(e, k), -z(e, g), w(k, g)])
    for k in range(B):
        for g, h in itertools.combinations(range(t), 2):
            s.add_clause([-w(k, g), -w(k, h)])
    for i, j in conf:
        for k in range(B):
            s.add_clause([-y(i, k), -y(j, k)])
    for i, j in share:
        for g in range(t):
            s.add_clause([-z(i, g), -z(j, g)])
    # symmetry: the edges at the first vertex get groups 0,1,.. and colours 0,1,..
    v0 = min(adj)
    star = [e for e in range(m) if v0 in E[e]]
    for r, e in enumerate(star):
        s.add_clause([z(e, r)]); s.add_clause([y(e, r)])
    if budget:
        s.conf_budget(budget)
        res = s.solve_limited()
    else:
        res = s.solve()
    s.delete()
    return res


def edge_colourable(edges, k):
    E, adj, share, conf = structure(edges)
    s = Cadical153(); x = lambda e, c: 1 + e * k + c
    for e in range(len(E)):
        s.add_clause([x(e, c) for c in range(k)])
    for i, j in share:
        for c in range(k):
            s.add_clause([-x(i, c), -x(j, c)])
    ok = s.solve()
    model = set(l for l in s.get_model() if l > 0) if ok else set()
    s.delete()
    return ok, (E, [next(c for c in range(k) if x(e, c) in model) for e in range(len(E))] if ok else None)


def chi(nb, kmax=6):
    """Chromatic number of a small graph given as adjacency lists (SAT, k = 1..kmax)."""
    n = len(nb)
    if n == 0:
        return 0
    for k in range(1, kmax + 1):
        s = Cadical153(); x = lambda v, c: 1 + v * k + c
        for v in range(n):
            s.add_clause([x(v, c) for c in range(k)])
            for u in nb[v]:
                if u > v:
                    for c in range(k):
                        s.add_clause([-x(v, c), -x(u, c)])
        ok = s.solve(); s.delete()
        if ok:
            return k
    return None


def job(args):
    n, idx, edges = args
    r4 = property_m(edges, 4, 20, budget=200000)
    r5 = None if r4 else property_m(edges, 5, 20, budget=200000)
    c1 = None if r4 else edge_colourable(edges, 4)[0]
    return n, idx, r4, r5, c1


def strong_colourable(edges, k, budget=None):
    E, adj, share, conf = structure(edges)
    s = Cadical153(); x = lambda e, c: 1 + e * k + c
    for e in range(len(E)):
        s.add_clause([x(e, c) for c in range(k)])
    for i, j in conf:
        for c in range(k):
            s.add_clause([-x(i, c), -x(j, c)])
    v0 = min(adj)  # the edges at one vertex form a clique: fix their colours
    for r, e in enumerate([e for e in range(len(E)) if v0 in E[e]]):
        s.add_clause([x(e, r)])
    if budget:
        s.conf_budget(budget); ok = s.solve_limited()
    else:
        ok = s.solve()
    s.delete()
    return ok


def tight_job(args):
    n, idx, edges = args
    t = 4 if edge_colourable(edges, 4)[0] else 5
    out = {}
    for B in (19, 18):
        out[B] = property_m(edges, t, B, budget=300000)
        if not out[B]:
            break
    return n, idx, t, out


def tight(N):
    """Does property M already hold with 19 (and 18) colours?  Lists every graph where it is not
    shown SAT (UNSAT or conflict budget exhausted)."""
    t0 = time.time()
    tasks = [(n, i, g) for n in range(5, N + 1) for i, g in enumerate(load(n))]
    stats = {}
    not19, not18 = [], []
    with mp.Pool() as pool:
        for n, idx, t, out in pool.imap_unordered(tight_job, tasks, chunksize=8):
            st = stats.setdefault(n, {"graphs": 0, "M@19": 0, "M@18": 0})
            st["graphs"] += 1
            if out.get(19):
                st["M@19"] += 1
            else:
                not19.append((n, idx, t, out.get(19)))
            if out.get(18):
                st["M@18"] += 1
            elif out.get(19):
                not18.append((n, idx, t, out.get(18)))
    for n in sorted(stats):
        print(n, stats[n], flush=True)
    print("not shown at 19 (n, index, t, result):", not19)
    print("shown at 19 but not at 18:", not18[:40], f"({len(not18)} total)")
    print(f"[{time.time() - t0:.0f}s]")


def small(N):
    t0 = time.time()
    tasks = [(n, i, g) for n in range(5, N + 1) for i, g in enumerate(load(n))]
    stats = {}
    bad = []
    with mp.Pool() as pool:
        for n, idx, r4, r5, c1 in pool.imap_unordered(job, tasks, chunksize=8):
            st = stats.setdefault(n, {"graphs": 0, "M4": 0, "class2": 0, "class1_not_M4": 0,
                                      "M5_after_M4_fail": 0, "unknown": 0})
            st["graphs"] += 1
            if r4:
                st["M4"] += 1
                continue
            if r4 is None or (r5 is None and not r4):
                st["unknown"] += 1
            if c1 is False:
                st["class2"] += 1
            elif c1:
                st["class1_not_M4"] += 1; bad.append((n, idx, "class1 without M4"))
            if r5:
                st["M5_after_M4_fail"] += 1
            elif r5 is False:
                bad.append((n, idx, "M5 fails"))
    for n in sorted(stats):
        print(n, stats[n], flush=True)
    print("exceptions:", bad[:50], f"({len(bad)} total)")
    print(f"[{time.time() - t0:.0f}s]")


def slack(n, g, seeds):
    sys.path.insert(0, ".")
    from exp18_large_girth import random_graph, girth as girth_of
    for seed in range(seeds):
        adj = random_graph(n, g, seed)
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        gg = girth_of(adj)
        ok, (E, col) = edge_colourable(edges, 4)
        if not ok:
            print({"seed": seed, "girth": gg, "class": 2}); continue
        chis = []
        for c in range(4):
            M = [E[i] for i in range(len(E)) if col[i] == c]
            at = {x: j for j, e in enumerate(M) for x in e}
            nb = [set() for _ in M]
            for j, (u, v) in enumerate(M):
                for x in (u, v):
                    for y in adj[x]:
                        if y in at and at[y] != j:
                            nb[j].add(at[y])
            chis.append((max(len(a) for a in nb), chi([sorted(a) for a in nb])))
        m16 = property_m(edges, 4, 16, budget=2000000)
        print({"seed": seed, "n": n, "m": len(edges), "girth": gg,
               "H(M_i) (maxdeg, chi) for one 4-edge-colouring": chis, "M4 with 16 colours": m16},
              flush=True)


# ---------------------------------------------------------------------------------------------
# exact mode for class-1 graphs on an even number of vertices: every class of a 4-edge-colouring
# is a perfect matching, so min over 1-factorisations of sum chi(H(M_i)) can be enumerated.

def perfect_matchings(n, E):
    at = [[i for i, e in enumerate(E) if v in e] for v in range(n)]
    out = []

    def rec(used_v, chosen):
        free = next((v for v in range(n) if v not in used_v), None)
        if free is None:
            out.append(frozenset(chosen)); return
        for i in at[free]:
            u, v = E[i]
            if u not in used_v and v not in used_v:
                rec(used_v | {u, v}, chosen + [i])

    rec(frozenset(), [])
    return out


def exact_min_budget(edges):
    E, adj, share, conf = structure(edges)
    n = len(adj); confset = set(conf)
    pms = perfect_matchings(n, E)
    cost = {}
    for P in pms:
        P_ = sorted(P)
        nb = [[b for b in range(len(P_)) if b != a and (min(P_[a], P_[b]), max(P_[a], P_[b])) in confset]
              for a in range(len(P_))]
        cost[P] = chi(nb, kmax=7)
    best = [None]
    allE = frozenset(range(len(E)))

    def rec(left, chosen, total):
        if best[0] is not None and total >= best[0]:
            return
        if not left:
            best[0] = total; return
        e = min(left)
        for P in pms:
            if e in P and P <= left:
                rec(left - P, chosen + [P], total + cost[P])

    rec(allE, [], 0)
    return best[0], len(pms), sorted(set(cost.values()))


def exact_job(args):
    n, idx, edges = args
    if not edge_colourable(edges, 4)[0]:
        return n, idx, None, None, None
    b, npm, costs = exact_min_budget(edges)
    return n, idx, b, npm, costs


def exact(ns):
    t0 = time.time()
    tasks = [(n, i, g) for n in ns for i, g in enumerate(load(n))]
    hist = {}; at20 = []
    with mp.Pool() as pool:
        for n, idx, b, npm, costs in pool.imap_unordered(exact_job, tasks, chunksize=4):
            if b is None:
                continue
            hist[(n, b)] = hist.get((n, b), 0) + 1
            if b >= 19:
                at20.append((n, idx, b, npm, costs))
    for key in sorted(hist):
        print(f"n={key[0]}: exact min budget for M4 = {key[1]}: {hist[key]} graphs", flush=True)
    print("graphs with exact min budget >= 19 (n, index, B, #perfect matchings, chi values):")
    for r in sorted(at20):
        print("  ", r)
    print(f"[{time.time() - t0:.0f}s]")



if __name__ == "__main__":
    if sys.argv[1] == "small":
        small(int(sys.argv[2]))
    elif sys.argv[1] == "tight":
        tight(int(sys.argv[2]))
    elif sys.argv[1] == "exact":
        exact([int(v) for v in sys.argv[2].split(",")])
    else:
        slack(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
