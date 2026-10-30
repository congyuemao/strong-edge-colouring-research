"""exp24: property R -- the colour structure of Theorem B, as a replacement target for property P.

Property R for a proper 5-edge-colouring M_1..M_5 of G:
  * R = M_5 is an induced matching (no edge of G joins two R-edges);
  * K = M_4 satisfies Delta(H(K)) <= 5 (every K-edge conflicts with at most 5 other K-edges);
  * M_1, M_2, M_3 are unconstrained.
With girth(G) >= 69: H(M_1..M_3) have Delta <= 6 and girth >= 35 (5 colours each by K6), H(K) has
Delta <= 5 (4 colours by K5), R takes 1 colour: chi'_s(G) <= 5+5+5+4+1 = 20 -- the same threshold
as property P (LARGE_GIRTH section 9.2), but only two of the five classes are constrained.  The
colouring built in the proof of Theorem B has property R.

SAT encoding: x(e,c) edge colours (proper).  R induced: no two R-edges at distance 1.  K: for every
edge e, if x(e,K) then at most 5 of the edges at distance exactly 1 from e have colour K
(sequential-counter cardinality constraint, every clause guarded by -x(e,K)); at girth >= 5 this is
'some outer neighbour of e misses K'.

Modes
  small N          all connected quartic graphs on 5..N vertices (graphs_n*.txt)
  random n g s     s random graphs with max degree 4 and girth >= g (exp18_large_girth.random_graph)
  fixedD n g s sep [strategy] [alt]
                   Theorem B's construction with the defect set D only required to be pairwise at
                   distance >= sep (sep = 2: D is an induced matching).  F1, F2, D and the 3/4
                   alternation of F2 - D are then fixed and SAT decides whether a set I of M_4-edges
                   exists with D + I induced and Delta(H(M_4 - I)) <= 5.  strategy: 'random' picks
                   a random admissible D-edge per odd cycle, 'cluster' prefers edges close to the
                   D-edges already chosen (adversarial).  alt = 'free' lets SAT also flip the
                   alternation of each component of F2 - D.  L > 0 uses cycles_graph (F1, F2 all
                   odd L-cycles: the densest defect set) instead of a random graph.
  dead n L g seed sep      dead M_4-edges (no admissible dominator at all) and the D-edges behind them
  resample n L g seeds sep re-choose D-edges near dead edges (Moser-Tardos style), then ask for I
  core n L g seed sep      minimal UNSAT core of the dominator problem once no edge is dead
  compare budget L,n,g ... property P (exp21) versus property R on cycles_graph instances
  tree rho seeds sep [din] [random|dead]
                   the dominator problem on a ball of the 4-regular tree (LARGE_GIRTH 10.5): D-edges
                   pairwise at distance >= sep inside radius din; 'dead' builds the sep-4 counterexample
"""
import multiprocessing as mp
import random
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

K, R, NC = 3, 4, 5   # colour indices: 0,1,2 free, 3 = K, 4 = R


def load(n):
    with open(f"graphs_n{n}.txt") as fh:
        for line in fh:
            yield [tuple(map(int, t.split("-"))) for t in line.split()]


def structure(edges):
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    E = [tuple(sorted(e)) for e in edges]
    at = {v: [] for v in adj}
    for i, (u, v) in enumerate(E):
        at[u].append(i); at[v].append(i)
    # edges at distance exactly 1 from e: share no vertex, joined by an edge of G
    near = []
    for i, (u, v) in enumerate(E):
        s = set()
        for x in (u, v):
            for y in adj[x]:
                if y in (u, v):
                    continue
                for j in at[y]:
                    a, b = E[j]
                    if u not in (a, b) and v not in (a, b):
                        s.add(j)
        near.append(sorted(s))
    return adj, E, at, near


def property_r(edges, budget=None):
    adj, E, at, near = structure(edges)
    m = len(E)
    pool = IDPool(start_from=m * NC + 1)
    x = lambda e, c: 1 + e * NC + c
    s = Cadical153()
    for e in range(m):
        s.add_clause([x(e, c) for c in range(NC)])
    for v, es in at.items():
        for i in range(len(es)):
            for j in range(i + 1, len(es)):
                for c in range(NC):
                    s.add_clause([-x(es[i], c), -x(es[j], c)])
    for e in range(m):
        for f in near[e]:
            if e < f:
                s.add_clause([-x(e, R), -x(f, R)])
        if len(near[e]) > 5:
            card = CardEnc.atmost([x(f, K) for f in near[e]], bound=5, vpool=pool,
                                  encoding=EncType.seqcounter)
            for cl in card.clauses:
                s.add_clause([-x(e, K)] + cl)
    v0 = min(at)
    for r, e in enumerate(at[v0]):
        s.add_clause([x(e, r)])
    if budget:
        s.conf_budget(budget); res = s.solve_limited()
    else:
        res = s.solve()
    if res:
        model = set(l for l in s.get_model() if l > 0)
        col = [next(c for c in range(NC) if x(e, c) in model) for e in range(m)]
        assert check(E, at, near, col), "decoded colouring violates property R"
    s.delete()
    return res


def check(E, at, near, col):
    """Independent check: proper, R induced, every K-edge has <= 5 conflicting K-edges."""
    for es in at.values():
        cs = [col[e] for e in es]
        if len(cs) != len(set(cs)):
            return False
    for e in range(len(E)):
        if col[e] == R and any(col[f] == R for f in near[e]):
            return False
        if col[e] == K and sum(1 for f in near[e] if col[f] == K) > 5:
            return False
    return True


def job(args):
    n, idx, edges = args
    t0 = time.time()
    return n, idx, property_r(edges, budget=2_000_000), time.time() - t0


def small(N):
    t0 = time.time()
    tasks = [(n, i, g) for n in range(5, N + 1) for i, g in enumerate(load(n))]
    stats, bad, slow = {}, [], 0.0
    with mp.Pool() as pool:
        for n, idx, r, dt in pool.imap_unordered(job, tasks, chunksize=8):
            st = stats.setdefault(n, {"graphs": 0, "R": 0, "not_R": 0, "unknown": 0})
            st["graphs"] += 1
            st["R" if r else ("not_R" if r is False else "unknown")] += 1
            if not r:
                bad.append((n, idx, r))
            slow = max(slow, dt)
    for n in sorted(stats):
        print(n, stats[n], flush=True)
    print("graphs without a property-R colouring (n, index, result):", sorted(bad)[:60],
          f"({len(bad)} total)")
    print(f"slowest instance {slow:.2f}s  [{time.time() - t0:.0f}s]")


def random_mode(n, g, seeds):
    from exp18_large_girth import random_graph, girth
    for seed in range(seeds):
        adj = random_graph(n, g, seed)
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        t0 = time.time()
        r = property_r(edges, budget=20_000_000)
        print({"seed": seed, "n": n, "m": len(edges), "girth": girth(adj),
               "deg<4": sum(len(a) < 4 for a in adj), "property R": r,
               "seconds": round(time.time() - t0, 1)}, flush=True)


# ---------------------------------------------------------------- Theorem B with a dense defect set

def cycles_graph(n, L, g, seed):
    """4-regular graph G = F1 + F2 where F1 and F2 are disjoint unions of L-cycles (L odd, so every
    cycle is odd and D is as dense as it can be: one edge per L/2 vertices), girth >= g."""
    from exp18_large_girth import near
    assert n % L == 0
    rng = random.Random(seed)
    for attempt in range(200):
        adj = [set() for _ in range(n)]
        F1 = []
        for s in range(0, n, L):
            for t in range(L):
                u, v = s + t, s + (t + 1) % L
                adj[u].add(v); adj[v].add(u); F1.append((u, v))
        free = set(range(n))
        F2 = []; ok = True
        while free and ok:
            for retry in range(30):       # build one L-cycle; undo it if it gets stuck
                v0 = rng.choice(sorted(free)); cyc = [v0]; added = []
                pool_ = sorted(free - {v0})
                while len(cyc) < L:
                    rng.shuffle(pool_)
                    nxt = next((u for u in pool_[:200] if u not in cyc
                                and not near(adj, cyc[-1], u, g - 2)), None)
                    if nxt is None:
                        break
                    adj[cyc[-1]].add(nxt); adj[nxt].add(cyc[-1]); added.append((cyc[-1], nxt))
                    cyc.append(nxt)
                if len(cyc) == L and not near(adj, cyc[-1], v0, g - 2):
                    adj[cyc[-1]].add(v0); adj[v0].add(cyc[-1]); added.append((cyc[-1], v0))
                    F2 += added; free -= set(cyc)
                    break
                for u, v in added:
                    adj[u].discard(v); adj[v].discard(u)
            else:
                ok = False
        if ok:
            return adj, [F1, F2]
    raise RuntimeError("no graph found")


def fixed_d(n, g, seed, sep, strategy="random", alt="fixed", L=0):
    from exp18_large_girth import random_graph, girth, split_two, components, ekey, ball, conflict
    if L:
        adj, F = cycles_graph(n, L, g, seed)
    else:
        adj = random_graph(n, g, seed)
        F = split_two(adj)
    gg = girth(adj)
    rng = random.Random(seed + 7)
    # odd cycles of F1, F2; choose one D-edge each, pairwise distance >= sep
    odd = [(j, es) for j in (0, 1) for seq, es, cyc in components(F[j]) if cyc and len(es) % 2]
    rng.shuffle(odd)
    D, Dj = [], []
    blocked = set()       # vertices within distance sep-1 of a chosen D-edge
    close = {}            # vertex -> distance to the nearest chosen D-edge (for 'cluster')
    for j, es in odd:
        cand = [e for e in es if not (set(e) & blocked)]
        if not cand:
            return {"seed": seed, "fail": "no admissible D-edge"}
        if strategy == "cluster":
            best = min(min(close.get(x, 99) for x in e) for e in cand)
            cand = [e for e in cand if min(close.get(x, 99) for x in e) == best]
        pick = rng.choice(cand)
        D.append(ekey(*pick)); Dj.append(j)
        for x, d in ball(adj, list(pick), max(sep - 1, 6)).items():
            if d <= sep - 1:
                blocked.add(x)
            close[x] = min(close.get(x, 99), d)
    Dset = set(D)
    # components of F2 - D2 (paths and even cycles) and their 3/4 alternation
    F2rest = [e for e in F[1] if ekey(*e) not in Dset]
    comps = [es for seq, es, cyc in components(F2rest)]
    M4, comp_of, parity = [], [], []
    for ci, es in enumerate(comps):
        for t, e in enumerate(es):
            M4.append(ekey(*e)); comp_of.append(ci); parity.append(t % 2)
    # with alt == 'fixed' only parity 1 edges are in M_4; with 'free' each component may flip
    # distances between D-edges (pairs within 7; each pair counted once)
    Dv = {x: k for k, e in enumerate(D) for x in e}
    dd = []
    for k, e in enumerate(D):
        best = {}
        for x, d in ball(adj, list(e), 7).items():
            if x in Dv and Dv[x] > k:
                best[Dv[x]] = min(best.get(Dv[x], 99), d)
        dd += best.values()
    near_D = set(x for e in D for x in ball(adj, list(e), 1))
    s = Cadical153(); pool = IDPool(start_from=1)
    inM4 = lambda i: pool.id(("m4", i))       # edge i of F2 - D2 is in M_4
    inI = lambda i: pool.id(("I", i))         # edge i is moved to R
    flip = lambda c: pool.id(("flip", c))
    for i in range(len(M4)):
        if alt == "fixed":
            s.add_clause([inM4(i)] if parity[i] else [-inM4(i)])
        else:     # parity 1 xor flip(component)
            a, b = inM4(i), flip(comp_of[i])
            if parity[i]:
                s.add_clause([-a, -b]); s.add_clause([a, b])
            else:
                s.add_clause([-a, b]); s.add_clause([a, -b])
        s.add_clause([-inI(i), inM4(i)])
        u, v = M4[i]
        if u in near_D or v in near_D:
            s.add_clause([-inI(i)])
    at4 = {}
    for i, (u, v) in enumerate(M4):
        at4.setdefault(u, []).append(i); at4.setdefault(v, []).append(i)
    # I independent in H(M_4): two I-edges joined by an edge of G
    for i, (u, v) in enumerate(M4):
        for x in (u, v):
            for y in adj[x]:
                for j in at4.get(y, []):
                    if j > i and not (set(M4[j]) & {u, v}):
                        s.add_clause([-inI(i), -inI(j)])
    # K = M_4 - I: every K-edge has an outer neighbour not covered by K.  w is uncovered by K iff no
    # edge of F2 - D2 at w is in M_4 - I.  unc(w) -> for each such edge: not in M_4 or in I.
    unc = lambda w: pool.id(("unc", w))
    for w in range(n):
        for i in at4.get(w, []):
            s.add_clause([-unc(w), -inM4(i), inI(i)])
    for i, (u, v) in enumerate(M4):
        outer = (adj[u] | adj[v]) - {u, v}
        s.add_clause([-inM4(i), inI(i)] + [unc(w) for w in outer])
    r = s.solve()
    s.delete()
    return {"seed": seed, "n": n, "girth": gg, "sep": sep, "strategy": strategy, "alt": alt,
            "odd cycles": len(D), "D in F1": Dj.count(0),
            "D-pairs at distance 2..7": {d: dd.count(d) for d in sorted(set(dd))},
            "I exists": r}


def dead_edges(adj, D, F):
    """M_4-edges (fixed alternation of F2 - D2) that no admissible I-edge can help: all outer
    neighbours covered by M_4, the edge itself conflicts with D, and so does every M_4-edge that
    covers one of its outer neighbours.  Returns (M4, list of (edge index, D-edges involved))."""
    from exp18_large_girth import components, ekey, ball
    Dset = set(D)
    M4 = []
    for seq, es, cyc in components([e for e in F[1] if ekey(*e) not in Dset]):
        M4 += [ekey(*e) for t, e in enumerate(es) if t % 2]
    cov = {x: i for i, e in enumerate(M4) for x in e}
    nearD = {}
    for k, e in enumerate(D):
        for x in ball(adj, list(e), 1):
            nearD.setdefault(x, set()).add(k)
    ND = lambda i: nearD.get(M4[i][0], set()) | nearD.get(M4[i][1], set())
    dead = []
    for i, (u, v) in enumerate(M4):
        outer = (adj[u] | adj[v]) - {u, v}
        if any(w not in cov for w in outer) or not ND(i):
            continue
        nb = [cov[w] for w in outer]
        if all(ND(j) for j in nb):
            dead.append((i, sorted(ND(i).union(*(ND(j) for j in nb)))))
    return M4, dead


def i_exists(adj, D, M4):
    """SAT: is there I in M_4 - N_D with D + I induced and Delta(H(M_4 - I)) <= 5?"""
    from exp18_large_girth import ball
    near_D = set(x for e in D for x in ball(adj, list(e), 1))
    cov = {x: i for i, e in enumerate(M4) for x in e}
    s = Cadical153(); y = lambda i: i + 1
    for i, (u, v) in enumerate(M4):
        if u in near_D or v in near_D:
            s.add_clause([-y(i)])
        nb = set()
        for x in (u, v):
            for t in adj[x]:
                j = cov.get(t)
                if j is not None and j != i:
                    nb.add(j)
                    if j > i:
                        s.add_clause([-y(i), -y(j)])
        outer = (adj[u] | adj[v]) - {u, v}
        if all(w in cov for w in outer):
            s.add_clause([y(i)] + [y(j) for j in nb])
    r = s.solve(); s.delete()
    return r


def resample_mode(n, L, g, seeds, sep):
    """Moser-Tardos style: choose D (pairwise distance >= sep) at random, and while some M_4-edge
    is dead, re-choose the D-edges of the odd cycles involved.  Then ask SAT for I."""
    from exp18_large_girth import components, ekey, ball, girth
    for seed in range(seeds):
        t0 = time.time()
        adj, F = cycles_graph(n, L, g, seed)
        rng = random.Random(seed + 11)
        odd = [(j, es) for j in (0, 1) for seq, es, cyc in components(F[j]) if cyc and len(es) % 2]
        D = [None] * len(odd)

        def admissible(k):
            others = set()
            for kk, e in enumerate(D):
                if kk != k and e is not None:
                    others |= set(ball(adj, list(e), sep - 1))
            return [ekey(*e) for e in odd[k][1] if not (set(e) & others)]

        for k in rng.sample(range(len(odd)), len(odd)):
            cand = admissible(k)
            if not cand:
                break
            D[k] = rng.choice(cand)
        if None in D:
            print({"seed": seed, "fail": "no admissible D-edge"}, flush=True)
            continue
        rounds = 0; first = None
        while True:
            M4, dead = dead_edges(adj, D, F)
            if first is None:
                first = len(dead)
            if not dead or rounds >= 400:
                break
            rounds += 1
            for k in rng.sample(dead[0][1], len(dead[0][1])):
                cand = admissible(k)
                if cand:
                    D[k] = rng.choice(cand)
        r = i_exists(adj, D, M4) if not dead else None
        print({"seed": seed, "n": n, "L": L, "girth": girth(adj), "sep": sep, "|D|": len(D),
               "dead edges initially": first, "resampling rounds": rounds, "dead at end": len(dead),
               "I exists": r, "seconds": round(time.time() - t0, 1)}, flush=True)


def dead_mode(n, L, g, seed, sep):
    """Count dead M_4-edges for a random D (pairwise distance >= sep) and list the D-edges that
    make them dead, with their pairwise distances."""
    from exp18_large_girth import components, ekey, ball, girth
    import collections
    adj, F = cycles_graph(n, L, g, seed)
    rng = random.Random(seed + 7)
    odd = [(j, es) for j in (0, 1) for seq, es, cyc in components(F[j]) if cyc and len(es) % 2]
    rng.shuffle(odd)
    D, Dj, blocked = [], [], set()
    for j, es in odd:
        cand = [e for e in es if not (set(e) & blocked)]
        if not cand:
            print({"seed": seed, "fail": "no admissible D-edge"}); return
        pick = rng.choice(cand); D.append(ekey(*pick)); Dj.append(j)
        blocked |= set(ball(adj, list(pick), sep - 1))
    M4, dead = dead_edges(adj, D, F)
    dist = lambda a, b: min(ball(adj, list(D[a]), 15).get(x, 99) for x in D[b])
    sizes = collections.Counter(len(inv) for _, inv in dead)
    print(f"n={n} L={L} sep={sep} girth={girth(adj)} |D|={len(D)} dead M4-edges={len(dead)}; "
          f"D-edges involved per dead edge: {dict(sorted(sizes.items()))}")
    for i, inv in dead[:4]:
        print("   dead", M4[i], "D-edges", [(D[k], "F1" if Dj[k] == 0 else "F2") for k in inv],
              "pairwise distances", [dist(a, b) for ai, a in enumerate(inv) for b in inv[ai + 1:]])


def core_mode(n, L, g, seed, sep):
    """Resample until no M_4-edge is dead; if I still does not exist, print a minimal set of
    domination constraints that cannot be satisfied together (UNSAT core, shrunk to minimal)."""
    from exp18_large_girth import components, ekey, ball
    adj, F = cycles_graph(n, L, g, seed)
    rng = random.Random(seed + 11)
    odd = [(j, es) for j in (0, 1) for seq, es, cyc in components(F[j]) if cyc and len(es) % 2]
    D = [None] * len(odd)

    def admissible(k):
        others = set()
        for kk, e in enumerate(D):
            if kk != k and e is not None:
                others |= set(ball(adj, list(e), sep - 1))
        return [ekey(*e) for e in odd[k][1] if not (set(e) & others)]

    for k in rng.sample(range(len(odd)), len(odd)):
        D[k] = rng.choice(admissible(k))
    while True:
        M4, dead = dead_edges(adj, D, F)
        if not dead:
            break
        for k in rng.sample(dead[0][1], len(dead[0][1])):
            cand = admissible(k)
            if cand:
                D[k] = rng.choice(cand)
    near_D = set(x for e in D for x in ball(adj, list(e), 1))
    cov = {x: i for i, e in enumerate(M4) for x in e}
    s = Cadical153(); m = len(M4); y = lambda i: i + 1
    nbs, dom = [], []
    for i, (u, v) in enumerate(M4):
        if u in near_D or v in near_D:
            s.add_clause([-y(i)])
        nb = set()
        for x in (u, v):
            for t in adj[x]:
                j = cov.get(t)
                if j is not None and j != i:
                    nb.add(j)
                    if j > i:
                        s.add_clause([-y(i), -y(j)])
        nbs.append(nb)
        if all(w in cov for w in (adj[u] | adj[v]) - {u, v}):
            dom.append(i); s.add_clause([-(m + len(dom)), y(i)] + [y(j) for j in nb])
    assum = [m + 1 + k for k in range(len(dom))]
    if s.solve(assumptions=assum):
        print({"seed": seed, "L": L, "sep": sep, "I exists": True}); return
    core = sorted(s.get_core()); shrunk = True
    while shrunk:
        shrunk = False
        for c in core:
            if not s.solve(assumptions=[d for d in core if d != c]):
                core = sorted(s.get_core()); shrunk = True; break
    crit = [dom[c - m - 1] for c in core]
    Dv = {x: k for k, e in enumerate(D) for x in e}
    inv = sorted({Dv[z] for i in crit for j in nbs[i] | {i} for x in M4[j]
                  for z in ball(adj, [x], 1) if z in Dv})
    dist = lambda a, b: min(ball(adj, list(a), 15).get(x, 99) for x in b)
    print({"seed": seed, "L": L, "sep": sep, "I exists": False,
           "minimal core: M4-edges whose domination constraints clash": [M4[i] for i in crit],
           "their pairwise distances": [dist(M4[a], M4[b]) for ai, a in enumerate(crit) for b in crit[ai + 1:]],
           "D-edges within distance 1 of them or their H4-neighbours": len(inv),
           "distance of each core edge to those D-edges": [[dist(M4[i], D[k]) for k in inv] for i in crit]})


# ---------------------------------------------------------------- the same question on the tree

def tree_mode(rho, seeds, sep, din=5, dmode="random"):
    """Ball of radius rho in the 4-regular tree, edges labelled F1/F2 (two of each at every vertex),
    M_4 = one F2-edge per vertex alternating along every F2-line.  D-edges (both types) are placed
    greedily at random, pairwise distance >= sep, inside radius din; for every D2-edge the
    alternation on one side is flipped so that exactly one endpoint of the D2-edge stays covered by
    M_4 (as on an odd cycle with one D-edge).  SAT then asks for I (in M_4 - N_D, independent in
    H(M_4)) dominating every M_4-edge within radius min(din + 3, rho - 2) of the root (I-edges may
    lie anywhere in the ball; with din <= rho - 5 every M_4-edge near a D-edge is constrained).
    dmode = 'dead': instead of a random D, the configuration of LARGE_GIRTH section 10.3 that makes
    an M_4-edge dead at sep = 4 (one D1-edge at an endpoint of h, three D-edges at distance 4)."""
    from collections import deque
    for seed in range(seeds):
        rng = random.Random(seed)
        par, depth, kind, adjl = [-1], [0], [None], [[]]   # kind of the edge to the parent
        E = []                                              # (u, v, type) with u parent of v
        q = deque([0])
        while q:
            v = q.popleft()
            if depth[v] == rho:
                continue
            need = {"F1": 2, "F2": 2}
            if kind[v]:
                need[kind[v]] -= 1
            for t in ("F1", "F2"):
                for _ in range(need[t]):
                    c = len(par); par.append(v); depth.append(depth[v] + 1); kind.append(t)
                    adjl.append([v]); adjl[v].append(c); E.append((v, c, t)); q.append(c)
        N = len(par)
        eid = {}
        for i, (u, v, t) in enumerate(E):
            eid[(u, v)] = eid[(v, u)] = i
        # M_4 status of F2-edges: alternate along lines
        K = {}
        for v in range(N):
            f2 = [eid[(v, c)] for c in adjl[v] if c != par[v] and E[eid[(v, c)]][2] == "F2"]
            if kind[v] == "F2":
                pe = eid[(par[v], v)]
                for e in f2:
                    K[e] = not K[pe]
            elif f2:
                b = rng.random() < 0.5
                K[f2[0]] = b
                if len(f2) > 1:
                    K[f2[1]] = not b

        def bfs(src, r):
            dist = {s: 0 for s in src}; dq = deque(src)
            while dq:
                x = dq.popleft()
                if dist[x] < r:
                    for y in adjl[x]:
                        if y not in dist:
                            dist[y] = dist[x] + 1; dq.append(y)
            return dist

        def line_side(e, end):
            """F2-edges of e's line beyond vertex end (not including e)."""
            out = []; prev, x = (E[e][0] if E[e][1] == end else E[e][1]), end
            while True:
                nxt = [y for y in adjl[x] if y != prev and E[eid[(x, y)]][2] == "F2"]
                if not nxt:
                    return out
                f = eid[(x, nxt[0])]; out.append(f); prev, x = x, nxt[0]

        D = []
        if dmode == "dead":
            # h = (u, v) an F2-edge in M_4; D1-edge at u; killers at distance 4 from u behind v
            u = 0
            h = next(eid[(0, c)] for c in adjl[0] if E[eid[(0, c)]][2] == "F2" and K[eid[(0, c)]])
            v = E[h][1]
            r1 = next(eid[(0, c)] for c in adjl[0] if E[eid[(0, c)]][2] == "F1")
            D.append(r1)
            for vi in adjl[v]:
                if vi == u:
                    continue
                # t_i = M_4-partner of v_i (away from v), then an edge at a neighbour of t_i
                ti = next(y for y in adjl[vi] if E[eid[(vi, y)]][2] == "F2" and K[eid[(vi, y)]])
                qi = next(y for y in adjl[ti] if y != vi)
                D.append(next(eid[(qi, y)] for y in adjl[qi] if y != ti and E[eid[(qi, y)]][2] == "F1"))
        else:
            cand = [i for i, (a, b, t) in enumerate(E) if depth[b] <= din]
            rng.shuffle(cand)
            blocked = set()
            for i in cand:
                a, b, t = E[i]
                if a in blocked or b in blocked:
                    continue
                D.append(i); blocked |= set(bfs([a, b], sep - 1))
        for i in D:
            a, b, t = E[i]
            if t == "F2":
                if K[i]:      # both ends were covered by this edge: flip b's side
                    for f in line_side(i, b):
                        K[f] = not K[f]
                else:         # both ends covered by their other F2-edges: flip a's side
                    for f in line_side(i, a):
                        K[f] = not K[f]
        Dset = set(D)
        M4 = [i for i, (a, b, t) in enumerate(E) if t == "F2" and K[i] and i not in Dset]
        cov = {}
        for i in M4:
            a, b, _ = E[i]
            assert a not in cov and b not in cov
            cov[a] = i; cov[b] = i
        for i in D:   # parity check: a D2-edge has exactly one endpoint covered by M_4
            a, b, t = E[i]
            if t == "F2":
                assert (a in cov) != (b in cov)
        near_D = set(bfs([x for i in D for x in E[i][:2]], 1))
        s = Cadical153(); idx = {i: k + 1 for k, i in enumerate(M4)}
        checked = 0
        for i in M4:
            a, b, _ = E[i]
            if a in near_D or b in near_D:
                s.add_clause([-idx[i]])
            nb = set()
            for x in (a, b):
                for y in adjl[x]:
                    j = cov.get(y)
                    if j is not None and j != i:
                        nb.add(j)
                        if j > i:
                            s.add_clause([-idx[i], -idx[j]])
            if max(depth[a], depth[b]) <= min(din + 3, rho - 2):
                outer = set(adjl[a]) | set(adjl[b])
                outer -= {a, b}
                if all(w in cov for w in outer):
                    checked += 1
                    s.add_clause([idx[i]] + [idx[j] for j in nb])
        r = s.solve(); s.delete()
        pairs = []
        for k, i in enumerate(D):
            dist = bfs(list(E[i][:2]), 7)
            for i2 in D[k + 1:]:
                dd = min(dist.get(x, 99) for x in E[i2][:2])
                if dd <= 7:
                    pairs.append(dd)
        print({"seed": seed, "rho": rho, "sep": sep, "D": dmode, "|D|": len(D),
               "D in F2": sum(E[i][2] == "F2" for i in D),
               "D-pairs at distance <= 7": {d: pairs.count(d) for d in sorted(set(pairs))},
               "M4-edges that must be dominated": checked, "I exists": r}, flush=True)


if __name__ == "__main__":
    sys.path.insert(0, ".")
    if sys.argv[1] == "resample":
        resample_mode(*map(int, sys.argv[2:7]))
        sys.exit()
    if sys.argv[1] in ("dead", "core"):
        (dead_mode if sys.argv[1] == "dead" else core_mode)(*map(int, sys.argv[2:7]))
        sys.exit()
    if sys.argv[1] == "compare":
        # P (exp21) versus R on graphs whose factor cycles are all odd L-cycles; budget per solve
        args = sys.argv[2:]
        sys.argv = sys.argv[:2]          # exp18 reads sys.argv[4] at import time
        from exp21_property_p import property_p
        from exp18_large_girth import girth
        budget = int(args[0])
        for spec in args[1:]:
            L, n, g = map(int, spec.split(","))
            adj, F = cycles_graph(n, L, g, 0)
            edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
            t0 = time.time(); p = property_p(edges, budget=budget)[0]; tp = time.time() - t0
            t0 = time.time(); r = property_r(edges, budget=budget); tr = time.time() - t0
            print({"L": L, "n": n, "girth": girth(adj), "property P": p, "P seconds": round(tp, 1),
                   "property R": r, "R seconds": round(tr, 1)}, flush=True)
        sys.exit()
    if sys.argv[1] == "tree":
        rho, seeds, sep = map(int, sys.argv[2:5])
        tree_mode(rho, seeds, sep, din=int(sys.argv[5]) if len(sys.argv) > 5 else 5,
                  dmode=sys.argv[6] if len(sys.argv) > 6 else "random")
        sys.exit()
    if sys.argv[1] == "small":
        small(int(sys.argv[2]))
    elif sys.argv[1] == "random":
        random_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif sys.argv[1] == "fixedD":
        n, g, seeds, sep = map(int, sys.argv[2:6])
        strategy = sys.argv[6] if len(sys.argv) > 6 else "random"
        alt = sys.argv[7] if len(sys.argv) > 7 else "fixed"
        L = int(sys.argv[8]) if len(sys.argv) > 8 else 0
        for seed in range(seeds):
            t0 = time.time()
            r = fixed_d(n, g, seed, sep, strategy, alt, L)
            r["L"] = L; r["seconds"] = round(time.time() - t0, 1)
            print(r, flush=True)
