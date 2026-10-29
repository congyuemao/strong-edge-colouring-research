"""Experiment 8: can a vertex of an odd cycle be 'stuck' in the universal high-girth local model?

Model: the 4-regular tree, ball of radius R around the root edge e0 = (0,1).  Edges get one of
K classes.  We encode NECESSARY conditions satisfied by any (Phi1, Phi2)-lexicographically minimal
K-partition of E(G) (G of large girth) in which e0 lies on an odd-cycle component of class 0
whose two cycle-neighbours of e0 are f and g:

 R1  every constrained edge w: d_own(w) <= d_c(w) for all classes c   (single-move Phi1 min)
 R2  e0, f, g are in class 0 with class-0 degree exactly 2; e0's class-0 neighbours are f, g
 R3  e in {e0,f,g}, class j != 0 with d_j(e) = 2, x a j-neighbour of e:  d_j(x) = 1
 R4  same:  d_k(x) >= 2 for k not in {0, j}, and d_0(x) >= 3           (two-move Phi1 min)
 R5  same, k not in {0,j} with d_k(x) = 2, z a k-neighbour of x:  d_k(z) = 1   (optional)

UNSAT for every (f, g) position means: in graphs whose girth exceeds the model diameter, a
lexicographically minimal partition has no odd cycle, i.e. property Q holds."""
import itertools
import sys
import time

import networkx as nx
from pysat.solvers import Cadical153


def tree_ball(R):
    """4-regular tree around root edge (0,1); returns graph and vertex depth (distance to edge)."""
    T = nx.Graph()
    T.add_edge(0, 1)
    depth = {0: 0, 1: 0}
    frontier = [0, 1]
    nxt = 2
    for d in range(1, R + 1):
        new = []
        for v in frontier:
            while T.degree(v) < 4:
                T.add_edge(v, nxt)
                depth[nxt] = d
                new.append(nxt)
                nxt += 1
        frontier = new
    return T, depth


class Model:
    def __init__(self, R, K):
        self.T, self.depth = tree_ball(R)
        self.R, self.K = R, K
        self.E = [tuple(sorted(e)) for e in self.T.edges()]
        self.idx = {e: i for i, e in enumerate(self.E)}
        self.top = 0
        self.s = Cadical153()
        self.x = {}
        for e in self.E:
            lits = []
            for c in range(K):
                self.top += 1
                self.x[e, c] = self.top
                lits.append(self.top)
            self.s.add_clause(lits)
            for a, b in itertools.combinations(lits, 2):
                self.s.add_clause([-a, -b])
        self.D = {}

    def edepth(self, e):
        return max(self.depth[e[0]], self.depth[e[1]])

    def complete(self, e):
        return self.edepth(e) <= self.R - 2

    def nbrs(self, e):
        a, b = e
        near = {a, b} | set(self.T[a]) | set(self.T[b])
        out = set()
        for w in near:
            for u in self.T[w]:
                f = tuple(sorted((w, u)))
                if f != e:
                    out.add(f)
        return sorted(out)

    def new(self):
        self.top += 1
        return self.top

    def degree_lits(self, e, c, cap=4):
        """D[e,c][k] <-> (#neighbours of e in class c) >= k, k = 1..cap (bidirectional counter)."""
        if (e, c) in self.D:
            return self.D[e, c]
        assert self.complete(e), e
        lits = [self.x[f, c] for f in self.nbrs(e)]
        prev = {}  # prev[k] literal for first i inputs >= k ; k=0 is True
        TRUE = None
        for i, l in enumerate(lits):
            cur = {}
            for k in range(1, min(cap, i + 1) + 1):
                v = self.new()
                cur[k] = v
                a = prev.get(k)            # first i-1 inputs >= k
                b = prev.get(k - 1) if k > 1 else TRUE  # >= k-1 (k=1: always true)
                # v <-> a or (b and l)
                if a is not None:
                    self.s.add_clause([-a, v])
                if k == 1:
                    self.s.add_clause([-l, v])
                    self.s.add_clause([-v, l] + ([a] if a is not None else []))
                else:
                    if b is not None:
                        self.s.add_clause([-b, -l, v])
                        self.s.add_clause([-v, b] + ([a] if a is not None else []))
                        self.s.add_clause([-v, l] + ([a] if a is not None else []))
                    else:
                        self.s.add_clause([-v] + ([a] if a is not None else []))
            prev = cur
        out = {k: prev.get(k) for k in range(1, cap + 1)}
        # missing k (fewer inputs than k) -> false
        for k in list(out):
            if out[k] is None:
                v = self.new()
                self.s.add_clause([-v])
                out[k] = v
        self.D[e, c] = out
        return out

    def R1(self, w):
        K = self.K
        D = {c: self.degree_lits(w, c) for c in range(K)}
        for c in range(K):
            xc = self.x[w, c]
            self.s.add_clause([-xc, -D[c][3]])
            for c2 in range(K):
                if c2 != c:
                    for k in (1, 2):
                        self.s.add_clause([-xc, -D[c][k], D[c2][k]])


SHORT = False


def build(R, K, f, g, use_R5):
    M = Model(R, K)
    e0 = (0, 1)
    s, x = M.s, M.x
    N0 = M.nbrs(e0)
    assert f in N0 and g in N0
    for e in (e0, f, g):
        s.add_clause([x[e, 0]])
    for n in N0:
        if n not in (f, g):
            s.add_clause([-x[n, 0]])
    constrained = {e0, f, g}
    for e in (e0, f, g):
        D0 = M.degree_lits(e, 0)
        s.add_clause([D0[2]])
        s.add_clause([-D0[3]])
    for e in (e0, f, g):
        M.R1(e)
        for j in range(1, K):
            Dj = M.degree_lits(e, j)
            if SHORT:
                # short closure: the two j-neighbours of e must conflict (else the closing even
                # path, plus e, is an induced cycle of length >= 4 in L^2, i.e. it is long)
                Ne = M.nbrs(e)
                for n, m in itertools.combinations(Ne, 2):
                    if m not in M.nbrs(n):
                        s.add_clause([-x[n, j], -x[m, j], Dj[3]])
            for n in M.nbrs(e):
                if not M.complete(n):
                    continue
                g1 = [-x[n, j], Dj[3]]  # clause prefix: (n in j and d_j(e) <= 2) -> ...
                Dn = {c: M.degree_lits(n, c) for c in range(K)}
                M.R1(n)
                s.add_clause(g1 + [-Dn[j][2]])
                s.add_clause(g1 + [Dn[j][1]])
                for k in range(1, K):
                    if k != j:
                        s.add_clause(g1 + [Dn[k][2]])
                s.add_clause(g1 + [Dn[0][3]])
                if use_R5:
                    for k in range(1, K):
                        if k == j:
                            continue
                        if SHORT:
                            Nn = [z for z in M.nbrs(n)]
                            for z1, z2 in itertools.combinations(Nn, 2):
                                if z2 not in M.nbrs(z1):
                                    s.add_clause(g1 + [-x[z1, k], -x[z2, k], Dn[k][3]])
                        for z in M.nbrs(n):
                            if not M.complete(z):
                                continue
                            Dz = M.degree_lits(z, k)
                            # n in j, d_j(e)=2, d_k(n)=2, z in k  ->  d_k(z) = 1
                            pre = g1 + [-Dn[k][2], Dn[k][3], -x[z, k]]
                            s.add_clause(pre + [-Dz[2]])
                            s.add_clause(pre + [Dz[1]])
    return M


def pair_types():
    # vertices: root edge (0,1); children of 0 are a's, children of 1 are b's (tree_ball numbering)
    T, depth = tree_ball(2)
    a = sorted(v for v in T[0] if v != 1)
    b = sorted(v for v in T[1] if v != 0)
    Ta = lambda i, t: tuple(sorted((a[i], sorted(w for w in T[a[i]] if w != 0)[t])))
    Tb = lambda i, t: tuple(sorted((b[i], sorted(w for w in T[b[i]] if w != 1)[t])))
    Su = lambda i: tuple(sorted((0, a[i])))
    Sv = lambda i: tuple(sorted((1, b[i])))
    return {
        "S(u),S(u)": (Su(0), Su(1)),
        "S(u),S(v)": (Su(0), Sv(0)),
        "S(u),T(a same)": (Su(0), Ta(0, 0)),
        "S(u),T(a other)": (Su(0), Ta(1, 0)),
        "S(u),T(b)": (Su(0), Tb(0, 0)),
        "T(a1),T(a1)": (Ta(0, 0), Ta(0, 1)),
        "T(a1),T(a2)": (Ta(0, 0), Ta(1, 0)),
        "T(a),T(b)": (Ta(0, 0), Tb(0, 0)),
    }


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    use_R5 = len(sys.argv) > 3 and "R5" in sys.argv[3]
    SHORT = len(sys.argv) > 3 and "short" in sys.argv[3]
    for name, (f, g) in pair_types().items():
        t0 = time.time()
        M = build(R, K, f, g, use_R5)
        ok = M.s.solve()
        print(f"K={K} R={R} R5={use_R5}  cycle-neighbours {name:16s}: {'SAT (local stuck pattern exists)' if ok else 'UNSAT'}  vars={M.top} [{time.time()-t0:.1f}s]", flush=True)
        M.s.delete()
