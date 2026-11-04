"""exp52: can a tree-like ball block every k-colour peeling repair of a blocked edge h?  (NEW_DIRECTIONS 11.24)

Repair.  Let Y be a set of k colours, U_Y = h + the edges coloured from Y.  Peel from U_Y any edge within L^2-distance r of h
having fewer than k neighbours left in U_Y.  If h gets peeled, colouring back in reverse order with colours of Y colours h and
changes only edges of U_Y within distance r (exp51).

Pattern.  A peeling that succeeds gives a colour-free certificate: an order x_1, ..., x_t = h and sets A_i of at most k - 1
neighbours of x_i allowed to be alive when x_i goes.  With W = union of N(x_i) - {x_1..x_{i-1}} - A_i - {h}, ANY colouring in
which W misses k colours Y has the repair for this Y, whatever the colours on the x_i and on the A_i.  (If x_i is not in U_Y,
it is simply absent, which only helps.)  So a colouring with no repair must use at least 21 - k colours on W.

CEGAR on the tree ball B(r + 1) (edges within L^2-distance r + 1 of h; distance r + 1 is frozen):
  master: proper 20-colouring of all edges but h, h blocked, every pattern found so far satisfied;
  check: for each k in KS and each Y, peel; each success gives a pattern, minimised and added.
SAT with no pattern left: a local configuration blocking all these repairs (re-checked at the end by a direct peeling and by
vertex relations).  UNSAT: every colouring of a tree-like ball has a k-colour repair within radius r, for some k in KS and Y.

Usage: exp52_peel_cegar.py <r> <k,k,...> <logdir> [max_rounds] [star=K] [tag=...]
"""
import itertools
import json
import os
import random
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

NC = 20


def tree_ball(R):
    """Edges of the 4-regular tree within L^2-distance R of the root edge (0, 1); list, and L^2 distance per edge."""
    D = 2 * R
    edges = [(0, 1)]
    frontier = [0, 1]
    n = 2
    for _ in range(D):
        nxt = []
        for x in frontier:
            for _ in range(3):
                edges.append((x, n))
                nxt.append(n)
                n += 1
        frontier = nxt
    inc = {}
    for i, (a, b) in enumerate(edges):
        inc.setdefault(a, []).append(i)
        inc.setdefault(b, []).append(i)
    adj = []
    for i, (a, b) in enumerate(edges):
        near = set(inc[a]) | set(inc[b])
        far = set(near)
        for j in near:
            for x in edges[j]:
                far.update(inc[x])
        far.discard(i)
        adj.append(far)
    dist = {0: 0}
    fr = [0]
    while fr:
        nx = []
        for x in fr:
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    nx.append(y)
        fr = nx
    return edges, adj, dist


def peel(adj, U, h, k, frozen):
    deg = {x: len(adj[x] & U) for x in U}
    alive = set(U)
    stack = sorted((x for x in U if deg[x] < k and x not in frozen), key=lambda x: (x != h, x))
    order = []
    while stack:
        x = stack.pop()
        if x not in alive:
            continue
        alive.discard(x)
        order.append(x)
        if x == h:
            return order
        for y in adj[x] & alive:
            deg[y] -= 1
            if deg[y] < k and y not in frozen:
                stack.append(y)
    return None


def pattern(adj, U, order, k, h, rng):
    """Minimal certificate from a successful peeling: returns W (frozenset)."""
    pos = {x: i for i, x in enumerate(order)}
    needed = {h}
    A = {}
    for x in reversed(order):
        if x not in needed:
            continue
        nbr = adj[x] & U
        earlier = [y for y in nbr if pos.get(y, 10 ** 9) < pos[x]]
        alive = [y for y in nbr if pos.get(y, 10 ** 9) > pos[x]]
        room = k - 1 - len(alive)
        assert room >= 0
        rng.shuffle(earlier)
        keep = earlier[:room]
        A[x] = set(alive) | set(keep)
        needed.update(earlier[room:])
    P = sorted(needed, key=pos.get)
    W = set()
    seen = set()
    for x in P:
        W |= adj[x] - seen - A[x]
        seen.add(x)
    W -= {h}
    return frozenset(W), P


def main():
    r = int(sys.argv[1])
    KS = [int(v) for v in sys.argv[2].split(",")]
    log = sys.argv[3]
    maxr = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
    star = next((int(a[5:]) for a in sys.argv[5:] if a.startswith("star=")), 0)
    tag = next((a[4:] for a in sys.argv[5:] if a.startswith("tag=")), "")
    os.makedirs(log, exist_ok=True)
    edges, adj, dist = tree_ball(r + 1)
    m = len(edges)
    h = 0
    # star states: further edges at vertex 0 stay uncoloured (removed as nodes, the conflicts they mediate stay)
    Ustar = [i for i, x in enumerate(edges) if 0 in x and i != h][:star]
    for g in Ustar:
        for y in adj[g]:
            adj[y].discard(g)
        adj[g] = set()
    hole = {h, *Ustar}
    coloured = [i for i in range(m) if i not in hole]
    frozen = {i for i in coloured if dist[i] > r}
    pool = IDPool()
    x = lambda i, c: pool.id(("x", i, c))
    for i in coloured:
        for c in range(NC):
            x(i, c)
    s = Cadical195()
    for i in coloured:
        s.add_clause([x(i, c) for c in range(NC)])
        for a, b in itertools.combinations(range(NC), 2):
            s.add_clause([-x(i, a), -x(i, b)])
        for j in adj[i]:
            if j > i and j not in hole:
                for c in range(NC):
                    s.add_clause([-x(i, c), -x(j, c)])
    mem = sorted(adj[h])
    for c in range(NC):
        s.add_clause([x(f, c) for f in mem])
    for pos, f in enumerate(mem):                        # colour symmetry: value precedence along N(h)
        for c in range(1, NC):
            s.add_clause([-x(f, c)] + [x(g, c - 1) for g in mem[:pos]])
    rng = random.Random(r * 1000 + sum(KS))
    known = {}
    name = f"exp52_r{r}_k{'_'.join(map(str, KS))}_s{star}{tag}"
    ck = os.path.join(log, name + ".jsonl")

    def add_pattern(W, k):
        key = (W, k)
        if key in known:
            return False
        known[key] = 1
        lits = []
        for c in range(NC):
            y = pool.id(("y", len(known), c))
            s.add_clause([-y] + [x(z, c) for z in W])
            lits.append(y)
        enc = CardEnc.atleast(lits, bound=NC + 1 - k, vpool=pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            s.add_clause(cl)
        return True

    if os.path.exists(ck):
        n = 0
        for line in open(ck, encoding="utf-8"):
            try:
                d = json.loads(line)
            except ValueError:
                continue
            n += add_pattern(frozenset(d["W"]), d["k"])
        print(f"resumed {n} patterns", flush=True)
    t0 = time.time()
    print(f"r={r} KS={KS} star={star}: {m} edges, {len(frozen)} frozen, N(h) coloured {len(mem)}", flush=True)
    out = open(ck, "a", encoding="utf-8")
    for rnd in range(1, maxr + 1):
        ts = time.time()
        if not s.solve():
            print(f"UNSAT at round {rnd}, {len(known)} patterns, {time.time() - t0:.0f} s", flush=True)
            json.dump({"result": "UNSAT", "patterns": len(known), "r": r, "KS": KS, "star": star},
                      open(os.path.join(log, name + "_result.json"), "w"))
            return
        model = set(v for v in s.get_model() if v > 0)
        col = {i: next(c for c in range(NC) if x(i, c) in model) for i in coloured}
        classes = [{i for i in coloured if col[i] == c} for c in range(NC)]
        added = fails = 0
        stats = {}
        for k in KS:
            new = 0
            for Y in itertools.combinations(range(NC), k):
                U = set().union(*(classes[c] for c in Y)) | {h}
                order = peel(adj, U, h, k, frozen)
                if order is None:
                    continue
                fails += 1
                W, P = pattern(adj, U, order, k, h, rng)
                assert not (W & U), "certificate not disjoint"
                if add_pattern(W, k):
                    out.write(json.dumps({"W": sorted(W), "k": k, "P": P}) + "\n")
                    added += 1
                    new += 1
            stats[k] = new
        out.flush()
        os.fsync(out.fileno())
        print(f"round {rnd}: repairs in this model {fails}, new patterns {stats}, total {len(known)}, "
              f"solve+check {time.time() - ts:.1f} s, elapsed {time.time() - t0:.0f} s", flush=True)
        if fails == 0:
            # independent re-check by vertex relations only
            nb = {}
            for a, b in edges:
                nb.setdefault(a, set()).add(b)
                nb.setdefault(b, set()).add(a)
            ids = {e: i for i, e in enumerate(edges)}
            for i, j in itertools.combinations(coloured, 2):
                if col[i] == col[j]:
                    a, b = edges[i]
                    assert not (set(edges[i]) & set(edges[j])) and not ((nb[a] | nb[b]) & set(edges[j])), (i, j)
            a, b = edges[h]
            seen = {col[i] for i in coloured if ((nb[a] | nb[b]) & set(edges[i]))}
            assert len(seen) == NC
            print(f"SAT: blocked, no repair for k in {KS} within radius {r}; witness checked; round {rnd}", flush=True)
            json.dump({"result": "SAT", "r": r, "KS": KS, "star": star, "colouring": {str(i): col[i] for i in coloured},
                       "edges": edges}, open(os.path.join(log, name + "_result.json"), "w"))
            return
    print("stopped at max rounds", flush=True)


main()
