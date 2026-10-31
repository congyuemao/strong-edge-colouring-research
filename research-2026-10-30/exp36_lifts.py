"""exp36: candidate counterexamples to Kempe insertion from covers (lifts) of C5[2].

C5[2] has L^2 = K20, so giving its 20 edges distinct colours is a strong 20-colouring in which every edge sees all
other colours.  In a k-lift G (random permutation voltages) the lifted colouring stays proper: two lifts of one base
edge are never within distance 1.  Every edge of G again sees all 19 other colours, so single recolourings never
help -- this is exactly the saturated regime -- and each bichromatic subgraph H_ab is a lift of the single base
conflict pq (a, b the colours of p, q): a union of paths and cycles.

Uncolouring a lift e~ of f leaves col(f) free (no lift of f conflicts with e~).  To block e~, recolour one conflict
g~ of e~ whose colour is repeated on N(e~) and which conflicts with no other lift of f to col(f).  Every such blocked
state is tested: number of separable pairs; 0 = stuck at depth 1, then depth 2 and BFS over swap sequences.

Usage: exp36_lifts.py k trials [seed]
"""
import random
import sys
import time
from collections import Counter

from exp33_kempe import K, l2_adj, separable, depth_two
from exp33b_adversary import deep_search


def base_c52():
    V = [(i, s) for i in range(5) for s in range(2)]
    E = [((i, s), ((i + 1) % 5, t)) for i in range(5) for s in range(2) for t in range(2)]
    return V, E


def lift(k, rng):
    V, E = base_c52()
    edges, proj = [], []
    for bi, (a, b) in enumerate(E):
        pi = list(range(k))
        rng.shuffle(pi)
        for j in range(k):
            edges.append(((a, j), (b, pi[j])))
            proj.append(bi)
    idx = {}
    for x in [(v, j) for v in V for j in range(k)]:
        idx[x] = len(idx)
    return [(idx[a], idx[b]) for a, b in edges], proj


def n_sep(adj, col, e):
    present = sorted({col[f] for f in adj[e]})
    return sum(1 for i, a in enumerate(present) for b in present[i + 1:]
               if separable(adj, col, e, a, b) is not None)


def main():
    k, trials = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    t0 = time.time()
    hist = Counter()
    stuck = 0
    for t in range(trials):
        edges, proj = lift(k, rng)
        if len(set(map(frozenset, edges))) < len(edges):
            continue                                            # multi-edge (cannot happen, kept as a guard)
        adj = l2_adj(edges)
        base_col = list(proj)
        for e in range(len(edges)):
            f = proj[e]
            others_f = [h for h in range(len(edges)) if proj[h] == f and h != e]
            cnt = Counter(base_col[g] for g in adj[e])
            for g in adj[e]:
                if cnt[base_col[g]] < 2 or any(h in adj[g] for h in others_f):
                    continue
                col = list(base_col)
                col[e] = -1
                col[g] = f
                assert all(col[x] != col[y] for x in range(len(edges)) if col[x] >= 0 for y in adj[x])
                if len({col[h] for h in adj[e]}) < K:
                    continue
                s = n_sep(adj, col, e)
                hist[s] += 1
                if s == 0:
                    stuck += 1
                    d2 = depth_two(adj, list(col), e)
                    print(f"k={k} trial {t} edge {e} recolour {g}: STUCK at depth 1; depth 2: "
                          f"{'repaired' if d2 else 'fails; BFS<=3: ' + str(deep_search(adj, col, e, 3))}", flush=True)
    print(f"k={k}: {trials} lifts, {sum(hist.values())} blocked states, stuck {stuck}; "
          f"min #separable {min(hist) if hist else None}; histogram (lowest) {sorted(hist.items())[:8]}  "
          f"[{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
