"""exp22: Kempe-chain local search for property P (LARGE_GIRTH section 9).

Property P for a proper 5-edge-colouring: an edge e of colour c is bad if it has 6 outer neighbours
and none of them misses c.  Moves (all keep the colouring proper):
  witness move  for a bad edge e of colour c, an outer neighbour w and a colour a missing at w:
                swap a <-> c on the (a,c)-Kempe chain that starts at w; afterwards w misses c.
  self move     for a bad edge e of colour c and a colour b != c: swap b <-> c on the (b,c)-chain
                through e; afterwards e has colour b.
Missing colours change only at the two ends of a swapped chain, so the change in the number of bad
edges is computed exactly from the chain edges and the edges next to the chain ends.

Descent: repeatedly apply a move that strictly lowers the number of bad edges (the best one found
for a random bad edge, scanning bad edges in random order).  A colouring where no move on any bad
edge lowers the count is a strict local minimum and is reported.

Usage: exp22_kempe.py n girth seeds [sideways] [depth2]
       exp22_kempe.py ball n girth seeds   (descend to a stuck state, then re-solve balls)
       exp22_kempe.py sanity n girth       (check the ball re-solver on known-repairable cases)
  sideways > 0 allows that many non-increasing moves per stuck state (plateau search);
  depth2 additionally tries every pair of consecutive moves when single moves are stuck.
"""
import random
import sys
import time

from pysat.solvers import Cadical153

K = 5


def proper_colouring(adj, edges):
    """Some proper 5-edge-colouring (SAT)."""
    at = {}
    for i, (u, v) in enumerate(edges):
        at.setdefault(u, []).append(i); at.setdefault(v, []).append(i)
    s = Cadical153(); x = lambda e, c: 1 + e * K + c
    for e in range(len(edges)):
        s.add_clause([x(e, c) for c in range(K)])
    for es in at.values():
        for i in range(len(es)):
            for j in range(i + 1, len(es)):
                for c in range(K):
                    s.add_clause([-x(es[i], c), -x(es[j], c)])
    assert s.solve()
    model = set(l for l in s.get_model() if l > 0)
    return [next(c for c in range(K) if x(e, c) in model) for e in range(len(edges))]


class State:
    def __init__(self, adj, edges, col):
        self.adj, self.E, self.col = adj, edges, col
        self.n = len(adj)
        self.eid = {}
        for i, (u, v) in enumerate(edges):
            self.eid[(u, v)] = i; self.eid[(v, u)] = i
        self.cat = [dict() for _ in range(self.n)]          # vertex -> {colour: edge}
        for i, (u, v) in enumerate(edges):
            self.cat[u][col[i]] = i; self.cat[v][col[i]] = i
        self.outer = []
        for (u, v) in edges:
            self.outer.append(tuple((self.adj[u] | self.adj[v]) - {u, v}))
        self.bad = set(i for i in range(len(edges)) if self.is_bad(i))

    def misses(self, w, c):
        return c not in self.cat[w]

    def is_bad(self, i):
        o = self.outer[i]
        if len(o) < 6:
            return False
        c = self.col[i]
        return not any(c not in self.cat[w] for w in o)

    def chain(self, start, a, b, first=None):
        """Edges of the (a,b)-Kempe component containing `start` (a vertex, or an edge if first)."""
        seen = set()
        if first is not None:
            stack = [first]
        else:
            stack = [self.cat[start][c] for c in (a, b) if c in self.cat[start]]
        while stack:
            e = stack.pop()
            if e in seen:
                continue
            seen.add(e)
            for x in self.E[e]:
                for c in (a, b):
                    f = self.cat[x].get(c)
                    if f is not None and f not in seen:
                        stack.append(f)
        return seen

    def affected(self, ch):
        """Edges whose badness can change when the chain `ch` is swapped."""
        deg = {}
        for e in ch:
            for x in self.E[e]:
                deg[x] = deg.get(x, 0) + 1
        ends = [x for x, d in deg.items() if d == 1]      # path ends (missing colour changes)
        aff = set(ch)
        for z in ends:
            for y in self.adj[z]:
                for f in self.cat[y].values():
                    aff.add(f)
        return aff

    def swap(self, ch, a, b):
        for e in ch:
            u, v = self.E[e]
            del self.cat[u][self.col[e]]; del self.cat[v][self.col[e]]
        for e in ch:
            u, v = self.E[e]
            self.col[e] = b if self.col[e] == a else a
            self.cat[u][self.col[e]] = e; self.cat[v][self.col[e]] = e

    def delta(self, ch, a, b):
        aff = self.affected(ch)
        before = sum(1 for f in aff if f in self.bad)
        self.swap(ch, a, b)
        after = sum(1 for f in aff if self.is_bad(f))
        self.swap(ch, a, b)
        return after - before, aff

    def apply(self, ch, a, b, aff):
        self.swap(ch, a, b)
        for f in aff:
            if self.is_bad(f):
                self.bad.add(f)
            else:
                self.bad.discard(f)

    def moves(self, i):
        c = self.col[i]
        for w in self.outer[i]:
            for a in range(K):
                if a != c and a not in self.cat[w]:
                    yield ("witness", self.chain(w, a, c), a, c)
        for b in range(K):
            if b != c:
                yield ("self", self.chain(None, b, c, first=i), b, c)


def depth2(st):
    """Look for two consecutive moves (each on a currently bad edge) that together lower the number
    of bad edges.  Returns the pair (as data to replay) or None."""
    base = len(st.bad)
    for i in list(st.bad):
        for kind1, ch1, a1, b1 in list(st.moves(i)):
            d1, aff1 = st.delta(ch1, a1, b1)
            if d1 < 0:
                return [(ch1, a1, b1, aff1)]
            saved = set(st.bad)
            st.apply(ch1, a1, b1, aff1)
            for j in list(st.bad):
                for kind2, ch2, a2, b2 in list(st.moves(j)):
                    d2, aff2 = st.delta(ch2, a2, b2)
                    if len(st.bad) + d2 < base:
                        st.swap(ch1, a1, b1); st.bad = saved
                        return [(ch1, a1, b1, aff1), (ch2, a2, b2, aff2)]
            st.swap(ch1, a1, b1); st.bad = saved
    return None


def descend(st, rng, sideways=0, max_steps=10 ** 7, use_depth2=False, stats=None):
    steps, chain_len, kinds = 0, [], {"witness": 0, "self": 0}
    side_left = sideways
    while st.bad and steps < max_steps:
        order = list(st.bad); rng.shuffle(order)
        best = None
        for i in order:
            for kind, ch, a, b in st.moves(i):
                d, aff = st.delta(ch, a, b)
                if best is None or d < best[0]:
                    best = (d, kind, ch, a, b, aff)
            if best and best[0] < 0:
                break
        if best[0] < 0 or (best[0] == 0 and side_left > 0):
            if best[0] == 0:
                side_left -= 1
            else:
                side_left = sideways
            d, kind, ch, a, b, aff = best
            st.apply(ch, a, b, aff); steps += 1
            chain_len.append(len(ch)); kinds[kind] += 1
        else:
            if use_depth2:
                pair = depth2(st)
                if pair is not None:
                    for ch, a, b, _ in pair:
                        aff = st.affected(ch)
                        st.apply(ch, a, b, aff); steps += 1
                    if stats is not None:
                        stats["depth2 escapes"] = stats.get("depth2 escapes", 0) + 1
                    side_left = sideways
                    continue
                if stats is not None:
                    stats["depth2 stuck"] = len(st.bad)
            return False, steps, chain_len, kinds
    return not st.bad, steps, chain_len, kinds


def main():
    sys.path.insert(0, ".")
    from exp18_large_girth import random_graph, girth
    n, g, seeds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    sideways = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    use_d2 = len(sys.argv) > 5 and sys.argv[5] == "depth2"
    for seed in range(seeds):
        rng = random.Random(seed)
        adj = random_graph(n, g, seed)
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        col = proper_colouring(adj, edges)
        st = State(adj, edges, col)
        # randomise the start with random Kempe swaps
        for _ in range(5 * len(edges)):
            e = rng.randrange(len(edges)); b = rng.randrange(K)
            if b != st.col[e]:
                st.swap(st.chain(None, b, st.col[e], first=e), b, st.col[e])
        st.bad = set(i for i in range(len(edges)) if st.is_bad(i))
        miss = [sum(1 for v in range(n) if c not in st.cat[v]) for c in range(K)]
        b0 = len(st.bad); t0 = time.time()
        stats = {}
        ok, steps, cl, kinds = descend(st, rng, sideways, use_depth2=use_d2, stats=stats)
        cl.sort()
        print({"seed": seed, "n": n, "girth": girth(adj), "start bad": b0, "start missing counts": miss,
               "reached P": ok, "final bad": len(st.bad), "moves": steps, "kinds": kinds,
               "chain length median/max": (cl[len(cl) // 2], cl[-1]) if cl else None, **stats,
               "seconds": round(time.time() - t0, 1)}, flush=True)


if __name__ == "__main__" and sys.argv[1] not in ("ball", "sanity"):
    main()


# ---------------------------------------------------------------------------------------------
# ball re-solving: can a stuck bad edge be fixed by recolouring only the edges within distance r,
# keeping every other edge fixed and every edge of the region good?

def ball_resolve(st, i, r, budget=2_000_000):
    from collections import deque
    u0, v0 = st.E[i]
    dist = {u0: 0, v0: 0}; q = deque([u0, v0])
    while q:
        x = q.popleft()
        for y in st.adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1; q.append(y)
    free = [e for e, (a, b) in enumerate(st.E) if dist.get(a, 10 ** 9) <= r and dist.get(b, 10 ** 9) <= r]
    check = [e for e, (a, b) in enumerate(st.E) if min(dist.get(a, 10 ** 9), dist.get(b, 10 ** 9)) <= r + 2]
    verts = set(x for e in check for x in st.E[e]) | set(w for e in check for w in st.outer[e])
    vid = {x: k for k, x in enumerate(sorted(verts))}
    eset = sorted(set(free) | set(check) | set(f for x in verts for f in st.cat[x].values()))
    loc = {e: k for k, e in enumerate(eset)}
    X = lambda e, c: 1 + loc[e] * K + c
    M = lambda w, c: 1 + len(eset) * K + vid[w] * K + c
    s = Cadical153()
    fs = set(free)
    for e in eset:
        if e in fs:
            s.add_clause([X(e, c) for c in range(K)])
        else:
            s.add_clause([X(e, st.col[e])])
    for x in verts:
        es = [f for f in st.cat[x].values()]
        # all edges at x (some may be outside eset only if x is far; include them by colour)
        es = [f for f in set(es) | set(e for e in eset if x in st.E[e]) if f in loc]
        for a in range(len(es)):
            for b in range(a + 1, len(es)):
                for c in range(K):
                    s.add_clause([-X(es[a], c), -X(es[b], c)])
        for c in range(K):
            for f in es:
                s.add_clause([-M(x, c), -X(f, c)])
    for e in check:
        o = st.outer[e]
        if len(o) < 6:
            continue
        for c in range(K):
            s.add_clause([-X(e, c)] + [M(w, c) for w in o])
    s.conf_budget(budget)
    res = s.solve_limited()
    s.delete()
    return res, len(free)


def ball_mode(n, g, seeds, radii=(1, 2, 3, 4)):
    sys.path.insert(0, ".")
    from exp18_large_girth import random_graph
    for seed in range(seeds):
        rng = random.Random(seed)
        adj = random_graph(n, g, seed)
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        st = State(adj, edges, proper_colouring(adj, edges))
        for _ in range(5 * len(edges)):
            e = rng.randrange(len(edges)); b = rng.randrange(K)
            if b != st.col[e]:
                st.swap(st.chain(None, b, st.col[e], first=e), b, st.col[e])
        st.bad = set(i for i in range(len(edges)) if st.is_bad(i))
        descend(st, rng, 0, use_depth2=True)
        res = {}
        for i in sorted(st.bad):
            res[i] = []
            for r in radii:
                ok, nf = ball_resolve(st, i, r)
                res[i].append((r, nf, ok))
                if ok:
                    break
        print({"seed": seed, "n": n, "stuck bad edges": len(st.bad),
               "least radius that fixes each (radius, free edges, result)": res}, flush=True)


def sanity_mode(n, g, cases=5):
    """Check ball_resolve on known-repairable cases: take a property-P colouring (SAT), apply one
    short Kempe swap that creates exactly one bad edge, and re-solve balls around that edge."""
    sys.path.insert(0, ".")
    from exp18_large_girth import random_graph
    from exp21_property_p import property_p  # noqa: F401  (same encoding, here re-done inline)
    adj = random_graph(n, g, 0)
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    at = {}
    for i, (u, v) in enumerate(edges):
        at.setdefault(u, []).append(i); at.setdefault(v, []).append(i)
    m = len(edges); x = lambda e, c: 1 + e * K + c; miss = lambda w, c: 1 + m * K + w * K + c
    s = Cadical153()
    for e in range(m):
        s.add_clause([x(e, c) for c in range(K)])
    for v, es in at.items():
        for a in range(len(es)):
            for b in range(a + 1, len(es)):
                for c in range(K):
                    s.add_clause([-x(es[a], c), -x(es[b], c)])
        for c in range(K):
            for f in es:
                s.add_clause([-miss(v, c), -x(f, c)])
    for e, (u, v) in enumerate(edges):
        o = (adj[u] | adj[v]) - {u, v}
        if len(o) == 6:
            for c in range(K):
                s.add_clause([-x(e, c)] + [miss(w, c) for w in o])
    assert s.solve()
    md = set(l for l in s.get_model() if l > 0)
    st = State(adj, edges, [next(c for c in range(K) if x(e, c) in md) for e in range(m)])
    print("bad edges in the starting property-P colouring:", len(st.bad), flush=True)
    rng = random.Random(1); found = 0
    for _ in range(5000):
        e = rng.randrange(m); b = rng.randrange(K)
        if b == st.col[e]:
            continue
        a0 = st.col[e]; ch = st.chain(None, b, a0, first=e)
        if len(ch) > 3:
            continue
        st.swap(ch, b, a0)
        bad = [i for i in range(m) if st.is_bad(i)]
        if len(bad) == 1:
            res = [ball_resolve(st, bad[0], r)[0] for r in (1, 2, 3)]
            print(f"swapping a chain of {len(ch)} edges created one bad edge {bad[0]}; "
                  f"ball re-solve at r = 1, 2, 3: {res}", flush=True)
            found += 1
        st.swap(ch, b, a0)
        if found >= cases:
            break


if __name__ == "__main__" and sys.argv[1] == "ball":
    ball_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
if __name__ == "__main__" and sys.argv[1] == "sanity":
    sanity_mode(int(sys.argv[2]), int(sys.argv[3]))
