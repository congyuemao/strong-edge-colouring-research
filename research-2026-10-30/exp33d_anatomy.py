"""exp33d: anatomy of the separable pairs that survive a long adversarial anneal (girth >= 6, tree-like N(e)).
Classifies each surviving pair by where its members sit in N(e) (near = shares an endpoint with e, far = joined to
e by an edge; far edges are grouped by the vertex of N(u) or N(v) they hang on) and by the size of the swapped
component."""
import random, sys, time
from collections import Counter
import networkx as nx
from exp33_kempe import K, l2_adj, separable
from exp33b_adversary import colour_all_but, anneal
from graphs_hg import random_girth

n, g, seed, rounds = map(int, sys.argv[1:5])
G = random_girth(n, g, seed)
edges = [tuple(x) for x in G.edges()]
adj = l2_adj(edges)
t0 = time.time()
rng = random.Random(seed)
for e in rng.sample(range(len(adj)), 2):
    u, v = edges[e]
    col = colour_all_but(adj, e, rng)
    for r in range(rounds):
        best, _ = anneal(adj, col, e, 40000, random.Random(100 * r + e), radius=3)
    def where(f):
        a, b = edges[f]
        if u in (a, b) or v in (a, b):
            return "near"
        hang = [x for x in (a, b) if G.has_edge(x, u) or G.has_edge(x, v)][0]
        return f"far@{hang}"
    if len({col[f] for f in adj[e]}) < K:
        print(f"edge {e}: not blocked at the end"); continue
    present = sorted({col[f] for f in adj[e]})
    kinds = Counter()
    lines = []
    for i, a in enumerate(present):
        for b in present[i + 1:]:
            comps = separable(adj, col, e, a, b)
            if comps is None:
                continue
            A = [where(f) for f in adj[e] if col[f] == a]
            B = [where(f) for f in adj[e] if col[f] == b]
            size = sum(len(c) for c in comps)
            kinds[("near" if any(x == "near" for x in A + B) else "far-far", size == len(A) or size == len(B))] += 1
            lines.append((a, b, A, B, size))
    mult = Counter(Counter(col[f] for f in adj[e]).values())
    print(f"n={n} girth={nx.girth(G)} edge {e}: {len(lines)} separable pairs after {rounds}x40000 steps; "
          f"colour multiplicities in N(e) {dict(mult)}; (position, trivial) counts {dict(kinds)}  [{time.time()-t0:.0f}s]")
    for l in lines[:12]:
        print("   ", l)
    sys.stdout.flush()
