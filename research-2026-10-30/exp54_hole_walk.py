"""exp54: insertion by hole moves alone (NEW_DIRECTIONS 11.24).
State (x, col): x uncoloured.  Hole move: p single at x with member f: col[x] = p, f uncoloured.  Search breadth first over states
for a hole with a free colour; no Kempe swaps at all.  Also reports, for the start colouring with the hole erased, the counts behind the
counting argument: n1, n2 (two-coloured components of size 1, 2), the number of non-single neighbours per edge, the size of the
one-step closure R in the digraph x -> y iff col[y] is single at x.
Usage: exp54_hole_walk.py [max_states] files.json...   (states as in the archive: edges, e, colouring)"""
import json, sys, os
from collections import Counter, deque
from exp33_kempe import K, l2_adj

def multiplicity(adj, col, x):
    c = Counter(col[y] for y in adj[x] if col[y] >= 0)
    return c

def search(adj, col, h, limit):
    col = list(col); col[h] = -1
    start = (h, tuple(col))
    seen = {start}
    q = deque([(h, col, 0)])
    while q and len(seen) < limit:
        x, c, d = q.popleft()
        m = multiplicity(adj, c, x)
        if len(m) < K:
            return d, len(seen)
        for y in adj[x]:
            if m[c[y]] == 1:
                n = list(c); n[x] = c[y]; n[y] = -1
                key = (y, tuple(n))
                if key not in seen:
                    seen.add(key)
                    q.append((y, n, d + 1))
    return None, len(seen)

def comps_small(adj, col):
    m = len(adj)
    n1 = n2 = 0
    nbc = [Counter(col[y] for y in adj[x] if col[y] >= 0) for x in range(m)]
    for x in range(m):
        if col[x] < 0: continue
        for b in range(K):
            if b == col[x]: continue
            if nbc[x][b] == 0:
                n1 += 1
            elif nbc[x][b] == 1:
                w = next(y for y in adj[x] if col[y] == b)
                if nbc[w][col[x]] == 1 and x < w:
                    n2 += 1
    return n1, n2, nbc

def main():
    limit = int(sys.argv[1])
    print("instance | m | n1 n2 | 2n1+n2 vs 2m | mean non-single per edge | closure R | depth to free colour, states")
    for f in sys.argv[2:]:
        d = json.load(open(f, encoding="utf-8"))
        for x in (d if isinstance(d, list) else [d]):
            edges = [tuple(e) for e in x["edges"]]
            h, col = x["e"], list(x["colouring"]); col[h] = -1
            adj = l2_adj(edges)
            n1, n2, nbc = comps_small(adj, col)
            ns = [sum(nbc[v][col[y]] >= 2 for y in adj[v] if col[y] >= 0) for v in range(len(adj))]
            R = {h}; st = [h]
            while st:
                v = st.pop()
                for y in adj[v]:
                    if col[y] >= 0 and nbc[v][col[y]] == 1 and y not in R:
                        R.add(y); st.append(y)
            dep, seen = search(adj, col, h, limit)
            print(x.get("instance", os.path.basename(f))[:34], len(adj), n1, n2, 2 * n1 + n2, 2 * len(adj), f"{sum(ns) / len(ns):.2f}", len(R), dep, seen, flush=True)

main()
