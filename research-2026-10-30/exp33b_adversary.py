"""exp33b: search for Kempe-stuck blocked edges (counterexamples to the one-pair / depth-2 form of KIL).

For a graph G and an edge e, start from a strong 20-colouring of G - e (conflicts in G; obtained by exp33's
Kempe greedy with e last) and anneal on
    energy = 10 * (#colours missing from N(e)) + #separable pairs at e,
with moves "recolour an edge within L^2-distance 2 of e to a free colour" and "Kempe swap at such an edge".
Energy 0 means e is blocked and no colour pair is separable: depth-1 stuck.  Such states are then tested at depth 2
(one arbitrary swap at N(e), then a one-pair move) and, if that fails too, by a breadth-first search over sequences of
swaps at N(e) up to a given depth.

Usage: exp33b_adversary.py random n girth graphs edges_per_graph steps
       exp33b_adversary.py small n graphs edges_per_graph steps      (graphs taken evenly from graphs_n<n>.txt)
"""
import math
import random
import sys
import time

from exp33_kempe import K, l2_adj, one_pair, depth_two, swap, component, separable, load


def free(adj, col, f):
    used = {col[g] for g in adj[f]}
    return [c for c in range(K) if c not in used]


def colour_all_but(adj, e, rng):
    """Strong 20-colouring of all edges except e, by Kempe greedy (None if it gets stuck)."""
    m = len(adj)
    col = [-1] * m
    order = [f for f in range(m) if f != e]
    rng.shuffle(order)
    for f in order:
        fr = free(adj, col, f)
        if not fr:
            mv = one_pair(adj, col, f)
            if mv is None:
                return None
            a, b, comps = mv
            for c in comps:
                swap(col, c, a, b)
            fr = free(adj, col, f)
        col[f] = rng.choice(fr)
    return col


def n_separable(adj, col, e):
    present = sorted({col[f] for f in adj[e] if col[f] >= 0})
    cnt = 0
    for i, a in enumerate(present):
        for b in present[i + 1:]:
            if separable(adj, col, e, a, b) is not None:
                cnt += 1
    return cnt


def energy(adj, col, e):
    miss = K - len({col[f] for f in adj[e] if col[f] >= 0})
    if miss:
        return 10 * miss + 190
    return n_separable(adj, col, e)


def anneal(adj, col, e, steps, rng, radius=2):
    region = set(adj[e])
    for _ in range(radius - 1):
        for f in list(region):
            region.update(adj[f])
    region.discard(e)
    region = sorted(region)
    E = energy(adj, col, e)
    best = E
    for t in range(steps):
        T = 2.0 * (1 - t / steps) + 0.05
        f = rng.choice(region)
        old = list(col)
        if rng.random() < 0.5:
            fr = [c for c in free(adj, col, f) if c != col[f]]
            if not fr:
                continue
            col[f] = rng.choice(fr)
        else:
            c = rng.randrange(K)
            if c == col[f]:
                continue
            swap(col, component(adj, col, f, col[f], c), col[f], c)
        E2 = energy(adj, col, e)
        if E2 <= E or rng.random() < math.exp((E - E2) / T):
            E = E2
            best = min(best, E)
            if E == 0:
                return 0, t
        else:
            col[:] = old
    return best, steps


def deep_search(adj, col, e, depth):
    """Is there a sequence of <= depth swaps (each at a component meeting N(e)) followed by a free colour at e?"""
    frontier = [list(col)]
    seen = {tuple(col[f] for f in adj[e])}
    for d in range(depth):
        nxt = []
        for c0 in frontier:
            present = sorted({c0[f] for f in adj[e]})
            for i, a in enumerate(present):
                for b in present[i + 1:]:
                    done = set()
                    for f in adj[e]:
                        if c0[f] not in (a, b) or f in done:
                            continue
                        comp = component(adj, c0, f, a, b)
                        done.update(comp)
                        c1 = list(c0)
                        swap(c1, comp, a, b)
                        if len({c1[g] for g in adj[e]}) < K:
                            return d + 1
                        key = tuple(c1[g] for g in adj[e])
                        if key not in seen:
                            seen.add(key)
                            nxt.append(c1)
        frontier = nxt
        if not frontier:
            break
    return None


def run(name, edges, n_edges, steps, rng, t0):
    adj = l2_adj(edges)
    cand = [e for e in range(len(adj)) if len(adj[e]) >= K]
    rng.shuffle(cand)
    found = 0
    for e in cand[:n_edges]:
        col = colour_all_but(adj, e, rng)
        if col is None:
            print(f"{name} edge {e}: Kempe greedy itself got stuck", flush=True)
            continue
        best, t = anneal(adj, col, e, steps, rng)
        if best > 0:
            print(f"{name} edge {e} (d={len(adj[e])}): min #separable pairs = {best}  [{time.time() - t0:.0f}s]",
                  flush=True)
            continue
        found += 1
        d2 = depth_two(adj, col, e)
        msg = f"{name} edge {e} (d={len(adj[e])}): DEPTH-1 STUCK after {t} steps; depth 2: "
        if d2 is not None:
            msg += "repaired"
        else:
            dd = deep_search(adj, col, e, 3)
            msg += f"fails; BFS over swap sequences: {'repaired at depth ' + str(dd) if dd else 'none up to depth 3'}"
        print(msg + f"  [{time.time() - t0:.0f}s]", flush=True)
    return found


if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time()
    rng = random.Random(7)
    if mode == "random":
        import networkx as nx
        from graphs_hg import random_girth
        n, g, ng, ne, steps = map(int, sys.argv[2:7])
        for s in range(ng):
            G = random_girth(n, g, s) if g > 3 else nx.random_regular_graph(4, n, seed=s)
            if G is None:
                continue
            run(f"n={n} girth={nx.girth(G)} seed={s}", [tuple(x) for x in G.edges()], ne, steps, rng, t0)
    else:
        n, ng, ne, steps = map(int, sys.argv[2:6])
        allg = list(load(n))
        for gi in range(0, len(allg), max(1, len(allg) // ng)):
            run(f"n={n} #{gi}", allg[gi], ne, steps, rng, t0)
