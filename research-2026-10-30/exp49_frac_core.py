"""exp49: the finite step of chi_f(L^2(G)) <= 20 for Delta(G) <= 4 (NEW_DIRECTIONS 11.21): a clique of L^2(G) with s edges
all of L2-degree >= 20 does not exist for s = 16 (and does for s = 15).

For y = ab with R = (N(a) | N(b)) - {a, b}, t = |N(a) & N(b)| and e' the number of edges inside R, the conflicts of y are the
edges other than y with an endpoint in R, so its L2-degree is sum_{w in R} deg(w) - e' <= 24 - 4t - e', and degree >= 20
forces 4t + e' <= 4.  Conflicts between members of Q use edges inside V(Q), and 4t + e' only grows from H = G[V(Q)] to G, so
it is enough to refute: a graph H with Delta <= 4 and Q inside E(H), |Q| >= s, pairwise conflicting in H, with
4t_H(y) + e'_H(y) <= 4 for each y in Q.

Fix z = uv in Q.  Every other member touches W = N[u] | N[v], so with T the endpoints outside W, |V(Q)| <= |W| + (s - 1).
Vertices: u = 0, v = 1, then A (other neighbours of u), B (other neighbours of v), then T.  Case tri: u, v have a common
neighbour (t(z) = 1; t(z) >= 2 is excluded by 4t <= 4), which is the last vertex of A and the first of B.
Symmetry breaking: rows of the T-by-(A, B) adjacency matrix lexicographically non-increasing, and columns within A and
within B too (the lexicographically largest matrix of an orbit satisfies both).

Mode control: every clique of edges of L2-degree >= 20 (a largest one per graph, sizes >= 12) of the connected 4-regular graphs on n
vertices must satisfy the encoding without symmetry breaking, with the graph given as assumptions.
Usage: exp49_frac_core.py <s> [tri|notri] [cadical|glucose] [nt=<|T|>] [dmin=<degree>] [dz=<bound on 4t + e' at z>]
       exp49_frac_core.py control <n,n,...> [limit]
"""
import itertools
import json
import sys
import time
from collections import Counter

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def build(s, tri, nT=None, dmin=20, dz=None, sym=True):
    """members have 4t + e' <= 24 - dmin; z = uv has 4t + e' <= dz if dz is given"""
    A = [2, 3, 4]
    B = [4, 5, 6] if tri else [5, 6, 7]
    W = sorted({0, 1} | set(A) | set(B))
    if nT is None:
        nT = s - 1
    T = list(range(max(W) + 1, max(W) + 1 + nT))
    V = W + T
    pool = IDPool()
    E = lambda i, j: pool.id(("E", min(i, j), max(i, j)))
    Qv = lambda i, j: pool.id(("Q", min(i, j), max(i, j)))
    pairs = list(itertools.combinations(V, 2))
    cl = []
    # neighbourhoods of u and v are fixed by the labelling
    for w in V:
        if w == 1:
            continue
        if w not in A:
            cl.append([-E(0, w)])
    for w in V:
        if w == 0:
            continue
        if w not in B:
            cl.append([-E(1, w)])
    cl.append([E(0, 1)])
    cl.append([Qv(0, 1)])
    if tri:
        cl.append([E(0, 4)])
        cl.append([E(1, 4)])
    # Q inside E(H); members of Q touch W; degrees <= 4
    qpairs = [(i, j) for i, j in pairs if i in W or j in W]
    for i, j in pairs:
        if (i, j) in qpairs:
            cl.append([-Qv(i, j), E(i, j)])
    qset = set(qpairs)
    for w in V:
        enc = CardEnc.atmost([E(w, x) for x in V if x != w], bound=4, vpool=pool, encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
    enc = CardEnc.atleast([Qv(i, j) for i, j in qpairs], bound=s, vpool=pool, encoding=EncType.totalizer)
    cl.extend(enc.clauses)
    # pairwise conflict
    for f, g in itertools.combinations(qpairs, 2):
        if set(f) & set(g):
            continue
        a, b = f
        c, d = g
        cl.append([-Qv(a, b), -Qv(c, d), E(a, c), E(a, d), E(b, c), E(b, d)])
    # 4t + e' <= 4 for each member
    for a, b in qpairs:
        y = Qv(a, b)
        rest = [w for w in V if w != a and w != b]
        In = {}
        Tri = []
        for w in rest:
            iw = pool.id(("In", a, b, w))
            In[w] = iw
            cl.append([-E(a, w), iw])
            cl.append([-E(b, w), iw])
            cl.append([-iw, E(a, w), E(b, w)])
            tw = pool.id(("Tri", a, b, w))
            cl.append([-E(a, w), -E(b, w), tw])
            Tri.append(tw)
        for t1, t2 in itertools.combinations(Tri, 2):
            cl.append([-y, -t1, -t2])
        anyt = pool.id(("AnyTri", a, b))
        for t1 in Tri:
            cl.append([-t1, anyt])
        terms = []
        for p, q in itertools.combinations(rest, 2):
            u_ = pool.id(("Eprime", a, b, p, q))
            cl.append([-In[p], -In[q], -E(p, q), u_])
            terms.append(u_)
        bound = 24 - dmin if dz is None or (a, b) != (0, 1) else dz
        if bound < 4:
            for t1 in Tri:
                cl.append([-y, -t1])
        enc = CardEnc.atmost(terms, bound=bound, vpool=pool, encoding=EncType.seqcounter)
        for c_ in enc.clauses:
            cl.append([-y] + c_)
        if bound >= 4:                                         # 4t + e' <= bound: a triangle leaves bound - 4 for e'
            enc = CardEnc.atmost(terms, bound=bound - 4, vpool=pool, encoding=EncType.seqcounter)
            for c_ in enc.clauses:
                cl.append([-y, -anyt] + c_)
    # symmetry breaking: double lex on the T x (A, B) matrix (T rows, columns within A and within B)
    def lex_ge(xs, ys):
        """xs >=lex ys, with auxiliary 'equal so far' variables"""
        eq = None
        for x, y_ in zip(xs, ys):
            pre = [] if eq is None else [-eq]
            cl.append(pre + [x, -y_])
            ne = pool.id(("lexeq", len(pool.obj2id)))
            if eq is None:
                cl.append([ne, x, y_])
                cl.append([ne, -x, -y_])
            else:
                cl.append([-eq, ne, x, y_])
                cl.append([-eq, ne, -x, -y_])
            eq = ne
    if not sym:
        return cl, pool, V, W, qpairs, E, Qv
    colsA = [w for w in A if not (tri and w == 4)]
    colsB = [w for w in B if not (tri and w == 4)]
    cols = colsA + ([4] if tri else []) + colsB
    for t1, t2 in zip(T, T[1:]):
        lex_ge([E(t1, c) for c in cols], [E(t2, c) for c in cols])
    for grp in (colsA, colsB):
        for c1, c2 in zip(grp, grp[1:]):
            lex_ge([E(t, c1) for t in T], [E(t, c2) for t in T])
    return cl, pool, V, W, qpairs, E, Qv


def check(V, edges, Q, s, dmin=20):
    """independent re-check of a model: only uses the edge lists"""
    nb = {w: set() for w in V}
    for a, b in edges:
        nb[a].add(b)
        nb[b].add(a)
    assert max(len(x) for x in nb.values()) <= 4
    assert len(Q) >= s and all(tuple(f) in {tuple(sorted(e)) for e in edges} for f in Q)
    for f, g in itertools.combinations(Q, 2):
        a, b = f
        c, d = g
        assert {a, b} & {c, d} or {c, d} & (nb[a] | nb[b]), (f, g)
    out = []
    for a, b in Q:
        t = len(nb[a] & nb[b])
        rest = (nb[a] | nb[b]) - {a, b}
        e1 = sum(1 for p, q in itertools.combinations(sorted(rest), 2) if q in nb[p])
        assert 4 * t + e1 <= 24 - dmin, (a, b, t, e1)
        out.append(4 * t + e1)
    return out


def largest_high_clique(edges):
    """a largest clique of L^2 among the edges of L2-degree >= 20; plain branching over bitsets"""
    nb = {}
    for a, b in edges:
        nb.setdefault(a, set()).add(b)
        nb.setdefault(b, set()).add(a)
    m = len(edges)
    adj = [0] * m
    for i, j in itertools.combinations(range(m), 2):
        a, b = edges[i]
        c, d = edges[j]
        if {c, d} & (nb[a] | nb[b]):
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    best = []

    def rec(cur, P):
        nonlocal best
        if len(cur) + bin(P).count("1") <= len(best):
            return
        if not P:
            best = list(cur)
            return
        while P:
            if len(cur) + bin(P).count("1") <= len(best):
                return
            v = (P & -P).bit_length() - 1
            rec(cur + [v], P & adj[v])
            P &= ~(1 << v)
    rec([], sum(1 << i for i in range(m) if bin(adj[i]).count("1") >= 20))
    return [edges[i] for i in best], nb


def control(n, limit):
    """a real clique must satisfy the encoding, with the graph on V(Q) given as assumptions"""
    done = Counter()
    with open(f"graphs_n{n}.txt") as f:
        for gi, line in enumerate(f):
            edges = [tuple(sorted(map(int, t.split("-")))) for t in line.split()]
            Qr, nb = largest_high_clique(edges)
            if len(Qr) < 12 or done["checked"] >= limit:
                continue
            a0, b0 = Qr[0]
            VQ = {x for f_ in Qr for x in f_}
            common = (nb[a0] & nb[b0]) & VQ
            tri = bool(common)
            A_ = sorted((nb[a0] & VQ) - {b0} - common)
            B_ = sorted((nb[b0] & VQ) - {a0} - common)
            T_ = sorted(VQ - {a0, b0} - set(A_) - set(B_) - common)
            lab = {a0: 0, b0: 1}
            if tri:
                lab[next(iter(common))] = 4
                lab.update(zip(A_, [2, 3]))
                lab.update(zip(B_, [5, 6]))
                base = 7
            else:
                lab.update(zip(A_, [2, 3, 4]))
                lab.update(zip(B_, [5, 6, 7]))
                base = 8
            lab.update(zip(T_, range(base, base + len(T_))))
            cl, pool, V, W, qpairs, E, Qv = build(len(Qr), tri, sym=False)
            inv = {v: k for k, v in lab.items()}
            assum = []
            for i, j in itertools.combinations(V, 2):
                on = i in inv and j in inv and inv[j] in nb[inv[i]]
                assum.append(E(i, j) if on else -E(i, j))
            for i, j in qpairs:
                on = i in inv and j in inv and tuple(sorted((inv[i], inv[j]))) in {tuple(sorted(f_)) for f_ in Qr}
                assum.append(Qv(i, j) if on else -Qv(i, j))
            with Solver(name="cadical195", bootstrap_with=cl) as sat:
                ok = sat.solve(assumptions=assum)
            done["checked"] += 1
            done[f"size {len(Qr)} {'satisfied' if ok else 'REJECTED'}"] += 1
    return dict(done)


if __name__ == "__main__":
    if sys.argv[1] == "control":
        for n in map(int, sys.argv[2].split(",")):
            print(f"n = {n}:", control(n, int(sys.argv[3]) if len(sys.argv) > 3 else 200), flush=True)
        sys.exit()
    s = int(sys.argv[1])
    cases = [sys.argv[2] == "tri"] if len(sys.argv) > 2 and sys.argv[2] in ("tri", "notri") else [False, True]
    solver = next((a for a in sys.argv[2:] if a in ("cadical", "glucose")), "cadical")
    nT = next((int(a[3:]) for a in sys.argv[2:] if a.startswith("nt=")), None)
    dmin = next((int(a[5:]) for a in sys.argv[2:] if a.startswith("dmin=")), 20)
    dz = next((int(a[3:]) for a in sys.argv[2:] if a.startswith("dz=")), None)
    name = {"cadical": "cadical195", "glucose": "glucose42"}[solver]
    for tri in cases:
        t0 = time.time()
        cl, pool, V, W, qpairs, E, Qv = build(s, tri, nT, dmin, dz)
        print(f"s={s} tri={tri} dmin={dmin} dz={dz} |V|={len(V)} vars={pool.top} clauses={len(cl)} encoded in {time.time() - t0:.1f}s", flush=True)
        with Solver(name=name, bootstrap_with=cl) as sat:
            ok = sat.solve()
            print(f"  {solver}: {'SAT' if ok else 'UNSAT'} in {time.time() - t0:.1f}s", flush=True)
            if ok:
                m = set(x for x in sat.get_model() if x > 0)
                edges = [(i, j) for i, j in itertools.combinations(V, 2) if E(i, j) in m]
                Q = [(i, j) for i, j in qpairs if Qv(i, j) in m]
                print("  re-check, 4t+e' per member:", sorted(check(V, edges, Q, s, dmin)), flush=True)
                print("  H:", json.dumps(edges), flush=True)
                print("  Q:", json.dumps(Q), flush=True)
