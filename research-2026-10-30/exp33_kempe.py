"""exp33: Kempe insertion in L^2 -- a Vizing-type route to chi'_s <= 20 for Delta <= 4.

Kempe insertion lemma (KIL, conjecture): let G have Delta <= 4 and let phi be a partial strong 20-colouring of G
(conflicts measured in G) with e uncoloured.  Then some sequence of Kempe swaps -- exchanging colours a, b on a
connected component of the subgraph of L^2[coloured edges] spanned by colours a, b -- leaves a colour free at e.
KIL gives chi'_s <= 20 by adding edges one at a time, at every girth.

Blocked edge e: all 20 colours occur on its conflict set N(e).  For a colour pair (a, b) let A, B be the a- and
b-coloured members of N(e).  Swapping every (a, b)-component that meets A frees a, unless some component meets both
A and B.  So the pair is "separable" iff no (a, b)-component meets both A and B; that is a one-pair move (the
components are disjoint, the swaps commute).  Depth 2: one swap on any component meeting N(e), then a one-pair move.

The test colours the edges in random order, a random free colour each time (spreading colours makes blocking more
likely); a blocked edge is repaired by the shallowest move found.  Unrepaired edges are left uncoloured and counted.

Colour choice: "spread" (default) picks the free colour new to most uncoloured neighbours' conflict sets.

Usage: exp33_kempe.py small n1,n2,..  reps  |  random n1,n2,.. girth reps
"""
import random
import sys
import time
from collections import Counter

K = 20


def l2_adj(edges):
    inc = {}
    for i, (a, b) in enumerate(edges):
        inc.setdefault(a, []).append(i)
        inc.setdefault(b, []).append(i)
    adj = []
    for i, (a, b) in enumerate(edges):
        near = set(inc[a]) | set(inc[b])
        far = set()
        for j in near:
            c, d = edges[j]
            far.update(inc[c])
            far.update(inc[d])
        far.discard(i)
        adj.append(sorted(far))
    return adj


def separable(adj, col, e, a, b):
    """Components (lists) to swap to free a colour at e via the pair (a, b), or None."""
    A = [f for f in adj[e] if col[f] == a]
    B = [f for f in adj[e] if col[f] == b]
    for side, other in ((A, B), (B, A)):
        other_set = set(other)
        seen, comps, ok = set(), [], True
        for s in side:
            if s in seen:
                continue
            comp, stack = [s], [s]
            seen.add(s)
            while stack and ok:
                x = stack.pop()
                for y in adj[x]:
                    if y not in seen and (col[y] == a or col[y] == b):
                        if y in other_set:
                            ok = False
                            break
                        seen.add(y)
                        comp.append(y)
                        stack.append(y)
            if not ok:
                break
            comps.append(comp)
        if ok:
            return comps
        # a component meets both A and B; the same component blocks the other side as well
        return None
    return None


def swap(col, comp, a, b):
    for x in comp:
        col[x] = b if col[x] == a else a


def one_pair(adj, col, e):
    present = sorted({col[f] for f in adj[e] if col[f] >= 0})
    for i, a in enumerate(present):
        for b in present[i + 1:]:
            comps = separable(adj, col, e, a, b)
            if comps is not None:
                return a, b, comps
    return None


def component(adj, col, s, a, b):
    comp, stack, seen = [s], [s], {s}
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen and (col[y] == a or col[y] == b):
                seen.add(y)
                comp.append(y)
                stack.append(y)
    return comp


def depth_two(adj, col, e):
    present = sorted({col[f] for f in adj[e] if col[f] >= 0})
    for i, a in enumerate(present):
        for b in present[i + 1:]:
            done = set()
            for f in adj[e]:
                if col[f] not in (a, b) or f in done:
                    continue
                comp = component(adj, col, f, a, b)
                done.update(comp)
                swap(col, comp, a, b)
                mv = one_pair(adj, col, e)
                if mv is not None:
                    return (a, b, comp), mv
                swap(col, comp, a, b)
    return None


def free_colours(adj, col, e):
    used = {col[f] for f in adj[e]}
    return [c for c in range(K) if c not in used]


def pick(adj, col, e, fr, rng, spread):
    """Random free colour, or (spread) one that is new to the conflict sets of the most uncoloured neighbours:
    this makes neighbourhoods rainbow and so produces many blocked edges."""
    if not spread:
        return rng.choice(fr)
    unc = [g for g in adj[e] if col[g] < 0]
    seen = [{col[h] for h in adj[g]} for g in unc]
    score = {c: sum(c in sg for sg in seen) for c in fr}
    best = min(score.values())
    return rng.choice([c for c in fr if score[c] == best])


def kempe_greedy(edges, rng, spread=True):
    adj = l2_adj(edges)
    m = len(edges)
    col = [-1] * m
    order = list(range(m))
    rng.shuffle(order)
    st = Counter()
    stuck = []
    for e in order:
        fr = free_colours(adj, col, e)
        if fr:
            col[e] = pick(adj, col, e, fr, rng, spread)
            continue
        st["blocked"] += 1
        mv = one_pair(adj, col, e)
        if mv is not None:
            a, b, comps = mv
            for c in comps:
                swap(col, c, a, b)
            st["depth1"] += 1
        else:
            mv2 = depth_two(adj, col, e)
            if mv2 is None:
                st["stuck"] += 1
                stuck.append((e, list(col)))
                continue
            (a, b, comp), (a2, b2, comps2) = mv2
            for c in comps2:
                swap(col, c, a2, b2)
            st["depth2"] += 1
        fr = free_colours(adj, col, e)
        assert fr, "move did not free a colour"
        col[e] = pick(adj, col, e, fr, rng, spread)
    for e in range(m):                                   # sanity: the final partial colouring is proper
        if col[e] >= 0:
            assert all(col[f] != col[e] for f in adj[e])
    return st, stuck


def load(n):
    with open(f"graphs_n{n}.txt") as f:
        for line in f:
            yield [tuple(map(int, t.split("-"))) for t in line.split()]


if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time()
    if mode == "small":
        reps = int(sys.argv[3])
        for n in map(int, sys.argv[2].split(",")):
            tot, worst = Counter(), []
            for gi, edges in enumerate(load(n)):
                for r in range(reps):
                    st, stuck = kempe_greedy(edges, random.Random(1000 * gi + r))
                    tot.update(st)
                    if stuck:
                        worst.append((gi, r, len(stuck)))
            print(f"n={n}: runs={reps}x; blocked={tot['blocked']} depth1={tot['depth1']} depth2={tot['depth2']} "
                  f"stuck={tot['stuck']}; graphs with stuck runs: {worst[:10]}  [{time.time() - t0:.0f}s]",
                  flush=True)
    elif mode == "random":
        import networkx as nx
        from graphs_hg import random_girth
        g, reps = int(sys.argv[3]), int(sys.argv[4])
        for n in map(int, sys.argv[2].split(",")):
            for s in range(reps):
                G = random_girth(n, g, s) if g > 3 else nx.random_regular_graph(4, n, seed=s)
                if G is None:
                    print(f"n={n} girth>={g} seed={s}: generation failed", flush=True)
                    continue
                edges = [tuple(e) for e in G.edges()]
                st, stuck = kempe_greedy(edges, random.Random(s))
                print(f"n={n} girth={nx.girth(G)} seed={s}: m={len(edges)} blocked={st['blocked']} "
                      f"depth1={st['depth1']} depth2={st['depth2']} stuck={st['stuck']}  [{time.time() - t0:.0f}s]",
                      flush=True)
