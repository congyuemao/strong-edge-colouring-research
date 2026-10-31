"""exp26: can a class triangle survive in a lex-minimal 9-class partition?  (NEW_DIRECTIONS section 1.9)

Setting (NEW_DIRECTIONS section 1): E(G) is split into 9 classes; the potential (Phi_1, #class triangles) is
lexicographically minimal, where Phi_1 = number of conflicting pairs inside a class.  Large girth is modelled by
a ball of the 4-regular tree around a class triangle T0 (WLOG in class 0).  Only valid consequences of
lex-minimality are encoded, so UNSAT is a proof that the configuration cannot occur:
  C1  for every constrained edge e (all its conflicts inside the ball): own class degree <= 2 and
      d_c(e) >= d_own(e) for every class c (moving e must not lower Phi_1);
  C2  T0 is a class-0 triangle (three pairwise conflicting class-0 edges; it is then a component);
  C3  lock: for every t in T0 and every class j != 0 with d_j(t) = 2, the two j-neighbours of t conflict and
      form a K2 component of class j.  Otherwise flipping t into j keeps Phi_1 (the flipped partition is still
      Phi_1-minimal, so those neighbours had j-degree <= 1) and destroys T0 without creating a new triangle.
Triangle positions in the tree (every L^2-triangle lies in some K(f) = star(u) + star(v)):
  star  three edges at one vertex;  path  edges of a P4;  fork  two edges at u plus an edge at another
  neighbour of u.

Modes
  single R          (a) is a locked class triangle possible?  for each position, ball radius R (R >= 4)
  pair R            (b) a second locked class triangle T1 (class 1 by symmetry) with an edge conflicting
                    with an edge of T0 (R >= 6).  If (b) is UNSAT, class triangles of a lex-minimiser are
                    pairwise non-conflicting, so one edge per triangle forms an induced matching.
  pairorb R         (b) one SAT call per orbit of T1 (tree automorphisms fixing T0, see canon), T1 within
                    eccentricity R - 2.
  pairpar R flip|noflip [w]
                    pairorb on w worker processes (default 8), one line per orbit as it finishes.
Append "flip" after R to add C1 in the flipped state (flipped_c1).
Every SAT answer is decoded and re-checked by an independent checker.
"""
import itertools
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

K = 9          # number of classes


def tree(depth):
    adj, dep, frontier, nxt = {0: []}, {0: 0}, [0], 1
    while frontier:
        new = []
        for v in frontier:
            if dep[v] == depth:
                continue
            for _ in range(4 - len(adj[v])):
                adj[v].append(nxt); adj[nxt] = [v]; dep[nxt] = dep[v] + 1
                new.append(nxt); nxt += 1
        frontier = new
    return adj


def position(adj, kind):
    n1, n2, n3 = adj[0][:3]
    child = lambda v, avoid: [w for w in adj[v] if w != avoid][0]
    if kind == "star":
        return [(0, n1), (0, n2), (0, n3)]
    if kind == "path":
        return [(0, n1), (0, n2), (n2, child(n2, 0))]
    if kind == "fork":
        return [(0, n1), (0, n2), (n3, child(n3, 0))]
    raise ValueError(kind)


class Ball:
    """Edges of the tree within distance R of a vertex set S, with their conflict lists."""

    def __init__(self, adj, S, R):
        dist, frontier = {v: 0 for v in S}, list(S)
        while frontier:
            new = []
            for v in frontier:
                for w in adj[v]:
                    if w not in dist:
                        dist[w] = dist[v] + 1
                        if dist[w] <= R:
                            new.append(w)
            frontier = new
        self.V = {v for v, d in dist.items() if d <= R}
        self.dist = dist
        self.E = sorted({tuple(sorted((v, w))) for v in self.V for w in adj[v] if w in self.V})
        self.idx = {e: i for i, e in enumerate(self.E)}
        at = {v: [] for v in self.V}
        for i, (a, b) in enumerate(self.E):
            at[a].append(i); at[b].append(i)
        self.conf = []
        for i, (a, b) in enumerate(self.E):
            close = {a, b} | {w for w in adj[a] + adj[b] if w in self.V}
            self.conf.append(sorted({j for v in close for j in at[v]} - {i}))
        self.confset = [set(c) for c in self.conf]
        self.at = at
        self.R = R

    def ecc(self, i):
        a, b = self.E[i]
        return max(self.dist[a], self.dist[b])


class Model:
    def __init__(self, ball, flip=False):
        self.flip = flip
        self.b, self.pool, self.cl = ball, IDPool(), []
        self.g = {}
        b = ball
        for i in range(len(b.E)):
            xs = [self.x(i, c) for c in range(K)]
            self.cl.append(xs)
            self.cl += [[-p, -q] for p, q in itertools.combinations(xs, 2)]
        self.constrained = [i for i in range(len(b.E)) if b.ecc(i) <= b.R - 2]
        for i in self.constrained:
            self.c1(i)

    def x(self, i, c):
        return self.pool.id(("x", i, c))

    def ge(self, i, c, t):
        """Literal equivalent to 'at least t conflicts of edge i lie in class c' (t = 1, 2)."""
        key = (i, c, t)
        if key in self.g:
            return self.g[key]
        v = self.pool.id(("g", i, c, t))
        lits = [self.x(j, c) for j in self.b.conf[i]]
        if t == 1:
            self.cl += [[v, -l] for l in lits]
            self.cl.append([-v] + lits)
        else:
            self.cl += [[v, -p, -q] for p, q in itertools.combinations(lits, 2)]
            self.cl += [[-v] + [l for l in lits if l != p] for p in lits]
        self.g[key] = v
        return v

    def ge3_upper(self, i, c):
        """Literal that implies 'at least 3 conflicts of edge i lie in class c'."""
        key = (i, c, 3)
        if key in self.g:
            return self.g[key]
        v = self.pool.id(("g3", i, c))
        self.g[key] = v
        lits = [self.x(j, c) for j in self.b.conf[i]]
        for p, q in itertools.combinations(range(len(lits)), 2):
            self.cl.append([-v] + [l for k, l in enumerate(lits) if k not in (p, q)])
        return v

    def c1(self, i):
        for c in range(K):
            enc = CardEnc.atmost([self.x(j, c) for j in self.b.conf[i]], bound=2, vpool=self.pool,
                                 encoding=EncType.seqcounter)
            self.cl += [[-self.x(i, c)] + cl for cl in enc.clauses]
        for c0 in range(K):
            for c in range(K):
                if c != c0:
                    for t in (1, 2):
                        self.cl.append([-self.x(i, c0), -self.ge(i, c0, t), self.ge(i, c, t)])

    def triangle(self, T, cls, guard=None):
        """T is a class-cls triangle (component) and locked; all clauses guarded by -guard if given."""
        b, gl = self.b, ([] if guard is None else [-guard])
        Ts = set(T)
        for t in T:
            self.cl.append(gl + [self.x(t, cls)])
            for m in b.conf[t]:
                if m not in Ts:
                    self.cl.append(gl + [-self.x(m, cls)])
        for t in T:
            for j in range(K):
                if j == cls:
                    continue
                g3 = self.ge3_upper(t, j)
                nb = [m for m in b.conf[t] if m not in Ts]
                for n1, n2 in itertools.combinations(nb, 2):
                    base = gl + [-self.x(n1, j), -self.x(n2, j), g3]
                    if n2 not in b.confset[n1]:
                        self.cl.append(base)
                    else:
                        for m in b.conf[n1]:
                            if m != n2:
                                self.cl.append(base + [-self.x(m, j)])
                        for m in b.conf[n2]:
                            if m != n1:
                                self.cl.append(base + [-self.x(m, j)])
                if self.flip:
                    self.flipped_c1(t, cls, j, nb, g3, gl)

    def flipped_c1(self, t, cls, j, nb, g3, gl):
        """C1 in S1 = S0 with t moved from cls to j, for every conflict m of t outside the triangle.

        If d_j(t) = 2 the flip keeps Phi_1, so S1 is again Phi_1-minimal and no single move may lower Phi_1
        there.  In S1 the degree of m in class c is d_c(m) + delta(c) with delta(cls) = -1, delta(j) = +1.
        Every clause carries g3 (which may be true only if d_j(t) >= 3), so it binds exactly when the flip is
        zero-cost.
        """
        delta = lambda c: (-1 if c == cls else 0) + (1 if c == j else 0)
        for m in nb:
            for cm in range(K):
                if cm == cls:
                    continue                      # C2: no other class-cls conflicts of t
                for c in range(K):
                    if c == cm:
                        continue
                    for s in (1, 2):              # own degree in S1 is at most 2
                        need_own, need = s - delta(cm), s - delta(c)
                        ante = [] if need_own <= 0 else [-self.ge(m, cm, need_own)]
                        if need <= 0:
                            continue
                        cons = self.ge(m, c, need) if need <= 2 else self.ge3_upper(m, c)
                        self.cl.append(gl + [g3, -self.x(m, cm)] + ante + [cons])

    def solve(self, budget=None):
        with Solver(name="cd15", bootstrap_with=self.cl) as s:
            ok = s.solve()
            model = s.get_model() if ok else None
        if not ok:
            return None
        pos = set(l for l in model if l > 0)
        return [next(c for c in range(K) if self.x(i, c) in pos) for i in range(len(self.b.E))]


def check(ball, cls, T_list, constrained, flip=False):
    """Independent re-check of C1, C2, C3 for a decoded class assignment."""
    deg = lambda i, c: sum(1 for j in ball.conf[i] if cls[j] == c)
    for i in constrained:
        own = deg(i, cls[i])
        assert own <= 2, ("own degree", i)
        assert all(deg(i, c) >= own for c in range(K)), ("C1", i)
    for T in T_list:
        c0 = cls[T[0]]
        assert all(cls[t] == c0 for t in T)
        assert all(b in ball.confset[a] for a, b in itertools.combinations(T, 2))
        for t in T:
            assert all(cls[m] != c0 for m in ball.conf[t] if m not in T), "not a component"
            for j in range(K):
                if j == c0 or deg(t, j) != 2:
                    continue
                x, y = [m for m in ball.conf[t] if cls[m] == j]
                assert y in ball.confset[x], ("lock: neighbours do not conflict", t, j)
                assert deg(x, j) == 1 and deg(y, j) == 1, ("lock: not a K2 component", t, j)
                if flip:
                    s1 = list(cls); s1[t] = j
                    d1 = lambda i, c: sum(1 for k in ball.conf[i] if s1[k] == c)
                    for m in ball.conf[t]:
                        if m in T:
                            continue
                        own = d1(m, s1[m])
                        assert own <= 2 and all(d1(m, c) >= own for c in range(K)), ("flipped C1", t, j, m)
    return True


def describe(ball, cls, T):
    out = []
    for t in T:
        d = [sum(1 for j in ball.conf[t] if cls[j] == c) for c in range(K)]
        zero = [j for j in range(K) if j != cls[t] and d[j] == 2]
        pairs = {j: [ball.E[m] for m in ball.conf[t] if cls[m] == j] for j in zero}
        out.append({"edge": ball.E[t], "class degrees": d, "zero-cost classes": zero, "partners": pairs})
    return out


def single(R, flip=False):
    for kind in ("star", "path", "fork"):
        adj = tree(R + 3)
        T_edges = position(adj, kind)
        S = {v for e in T_edges for v in e}
        ball = Ball(adj, S, R)
        T = [ball.idx[tuple(sorted(e))] for e in T_edges]
        assert all(b in ball.confset[a] for a, b in itertools.combinations(T, 2))
        m = Model(ball, flip)
        m.triangle(T, 0)
        t0 = time.time()
        cls = m.solve()
        res = {"mode": "single", "flip": flip, "position": kind, "R": R, "edges": len(ball.E),
               "constrained": len(m.constrained), "clauses": len(m.cl),
               "locked triangle possible": cls is not None, "seconds": round(time.time() - t0, 1)}
        if cls is not None:
            res["independent check"] = check(ball, cls, [T], m.constrained, flip)
            res["witness"] = describe(ball, cls, T)
        print(res, flush=True)


def triangles_near(ball, T0):
    """All L^2-triangles (inside some K(f)) disjoint from T0 with an edge conflicting with T0."""
    T0s, found = set(T0), set()
    near = {m for t in T0 for m in ball.conf[t]} - T0s
    for f in range(len(ball.E)):
        if ball.ecc(f) > 4:
            continue
        a, b = ball.E[f]
        star = sorted(set(ball.at[a]) | set(ball.at[b]))
        for T in itertools.combinations(star, 3):
            if T0s & set(T) or not (near & set(T)):
                continue
            found.add(T)
    return sorted(found)


def pair(R, flip=False):
    for kind in ("star", "path", "fork"):
        adj = tree(R + 3)
        T_edges = position(adj, kind)
        S = {v for e in T_edges for v in e}
        ball = Ball(adj, S, R)
        T0 = [ball.idx[tuple(sorted(e))] for e in T_edges]
        m = Model(ball, flip)
        m.triangle(T0, 0)
        cands = [T for T in triangles_near(ball, T0)
                 if all(ball.ecc(t) <= R - 4 for t in T)]
        sels = []
        for T in cands:
            s = m.pool.id(("sel", T))
            sels.append(s)
            m.triangle(list(T), 1, guard=s)
        m.cl.append(sels)
        t0 = time.time()
        cls = m.solve()
        res = {"mode": "pair", "flip": flip, "position": kind, "R": R, "edges": len(ball.E),
               "candidate T1": len(cands), "clauses": len(m.cl),
               "two conflicting locked triangles possible": cls is not None,
               "seconds": round(time.time() - t0, 1)}
        if cls is not None:
            T1 = next(list(T) for T in cands if all(cls[t] == 1 for t in T)
                      and all(cls[x] != 1 for t in T for x in ball.conf[t] if x not in T))
            res["independent check"] = check(ball, cls, [T0, T1], m.constrained, flip)
            res["T1"] = [ball.E[t] for t in T1]
            res["witness T0"] = describe(ball, cls, T0)
            res["witness T1"] = describe(ball, cls, T1)
        print(res, flush=True)


def canon(adj, T0e, T1e):
    """Canonical form of the subtree spanned by T0 and T1, edges marked A (T0), B (T1), - (other).

    Two candidates with the same form lie in one orbit of the tree automorphisms fixing T0 (an isomorphism
    between finite subtrees of the 4-regular tree extends to the whole tree), so one representative per
    form suffices.  Vertex ids grow with depth, so the parent of v != 0 is adj[v][0].
    """
    W = {v for e in T0e + T1e for v in e}
    par = lambda v: adj[v][0]
    depth = {}
    def d(v):
        if v not in depth:
            depth[v] = 0 if v == 0 else d(par(v)) + 1
        return depth[v]
    E = set()
    for u, v in itertools.combinations(sorted(W), 2):
        while u != v:
            if d(u) < d(v):
                u, v = v, u
            E.add(tuple(sorted((u, par(u))))); u = par(u)
    mark = {e: "-" for e in E}
    for e in T0e:
        mark[tuple(sorted(e))] = "A"
    for e in T1e:
        mark[tuple(sorted(e))] = "B"
    nb = {}
    for a, b in E:
        nb.setdefault(a, []).append(b); nb.setdefault(b, []).append(a)
    def rooted(v, p):
        return "(" + "".join(sorted(mark[tuple(sorted((v, c)))] + rooted(c, v) for c in nb[v] if c != p)) + ")"
    return min(rooted(v, None) for v in nb)


def pair_orbits(R, flip=False, kinds=("star", "path", "fork")):
    for kind in kinds:
        adj = tree(R + 3)
        T_edges = position(adj, kind)
        S = {v for e in T_edges for v in e}
        ball = Ball(adj, S, R)
        T0 = [ball.idx[tuple(sorted(e))] for e in T_edges]
        orbits = {}
        for T in triangles_near(ball, T0):
            if all(ball.ecc(t) <= R - 2 for t in T):
                orbits.setdefault(canon(adj, T_edges, [ball.E[t] for t in T]), T)
        base = Model(ball, flip)
        base.triangle(T0, 0)
        print({"mode": "pair-orbits", "flip": flip, "position": kind, "R": R, "edges": len(ball.E),
               "orbits": len(orbits), "base clauses": len(base.cl)}, flush=True)
        sat = []
        t0 = time.time()
        for n, (form, T1) in enumerate(sorted(orbits.items())):
            ncl, cache = len(base.cl), dict(base.g)
            base.triangle(list(T1), 1)
            cls = base.solve()
            del base.cl[ncl:]
            base.g = cache            # cached literals defined after ncl lost their clauses
            if cls is not None:
                ok = check(ball, cls, [T0, list(T1)], base.constrained, flip)
                sat.append({"T1": [ball.E[t] for t in T1], "max ecc": max(ball.ecc(t) for t in T1),
                            "independent check": ok})
        print({"position": kind, "R": R, "flip": flip, "orbits": len(orbits), "SAT orbits": len(sat),
               "seconds": round(time.time() - t0, 1), "SAT examples": sat[:5]}, flush=True)


_SETUP = {}


def _setup(R, flip, kind):
    """Per-process cache: ball, T0, sorted orbit representatives and the base model for one position."""
    key = (R, flip, kind)
    if key not in _SETUP:
        _SETUP.clear()                      # keep one base model per process (memory)
        adj = tree(R + 3)
        T_edges = position(adj, kind)
        ball = Ball(adj, {v for e in T_edges for v in e}, R)
        T0 = [ball.idx[tuple(sorted(e))] for e in T_edges]
        orbits = {}
        for T in triangles_near(ball, T0):
            if all(ball.ecc(t) <= R - 2 for t in T):
                orbits.setdefault(canon(adj, T_edges, [ball.E[t] for t in T]), T)
        base = Model(ball, flip)
        base.triangle(T0, 0)
        _SETUP[key] = (ball, T0, sorted(orbits.items()), base)
    return _SETUP[key]


def _orbit_job(job):
    R, flip, kind, n = job
    ball, T0, orbits, base = _setup(R, flip, kind)
    form, T1 = orbits[n]
    t0 = time.time()
    ncl, cache = len(base.cl), dict(base.g)
    base.triangle(list(T1), 1)
    cls = base.solve()
    del base.cl[ncl:]
    base.g = cache
    res = {"position": kind, "orbit": n, "form": form, "T1": [ball.E[t] for t in T1],
           "max ecc": max(ball.ecc(t) for t in T1), "SAT": cls is not None,
           "seconds": round(time.time() - t0, 1)}
    if cls is not None:
        res["independent check"] = check(ball, cls, [T0, list(T1)], base.constrained, flip)
        res["witness T0"] = describe(ball, cls, T0)
        res["witness T1"] = describe(ball, cls, list(T1))
    return res


def pair_orbits_par(R, flip=False, workers=8):
    """pair_orbits with one process per orbit; prints every orbit as it finishes."""
    import multiprocessing as mp
    jobs = []
    for kind in ("star", "path", "fork"):
        ball, T0, orbits, base = _setup(R, flip, kind)
        print({"mode": "pair-orbits-par", "flip": flip, "position": kind, "R": R, "edges": len(ball.E),
               "orbits": len(orbits), "base clauses": len(base.cl)}, flush=True)
        jobs += [(R, flip, kind, n) for n in range(len(orbits))]
    _SETUP.clear()
    summary, t0 = {}, time.time()
    with mp.Pool(workers) as pool:
        for res in pool.imap_unordered(_orbit_job, jobs):
            print(res, flush=True)
            s = summary.setdefault(res["position"], {"orbits": 0, "SAT": 0})
            s["orbits"] += 1; s["SAT"] += res["SAT"]
    print({"summary": summary, "flip": flip, "R": R, "seconds": round(time.time() - t0, 1)}, flush=True)


if __name__ == "__main__":
    mode, R = sys.argv[1], int(sys.argv[2])
    flip = len(sys.argv) > 3 and sys.argv[3] == "flip"
    if mode == "pairpar":
        pair_orbits_par(R, flip, int(sys.argv[4]) if len(sys.argv) > 4 else 8)
    else:
        {"single": single, "pair": pair, "pairorb": pair_orbits}[mode](R, flip)
