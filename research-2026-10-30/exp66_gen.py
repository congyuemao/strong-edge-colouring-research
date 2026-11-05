"""exp66: Delta = 3 testbed for the colour-set core conjectures (NEW_DIRECTIONS 11.27).
Writes starting states for exp66_set_core_K.c: a cubic graph, an edge h, a proper 10-colouring of L^2 - h (found by tabu search).
Usage: SE_D=3 SE_K=10 exp66_gen.py outdir n seed [count]   Files <outdir>/d<D>K<K>_n<n>_<seed>_<i>.in and .json"""
import json, os, random, sys
import networkx as nx
K = int(os.environ.get("SE_K", "10")); D = int(os.environ.get("SE_D", "3"))
def l2(edges):
    m = len(edges); adj = [set() for _ in range(m)]
    inc = {}
    for i, (p, q) in enumerate(edges):
        inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i)
    nb = {v: set() for v in inc}
    for p, q in edges:
        nb[p].add(q); nb[q].add(p)
    for i, (p, q) in enumerate(edges):
        s = set(inc[p]) | set(inc[q])
        for w in nb[p] | nb[q]:
            s |= inc[w]
        s.discard(i); adj[i] = s
    return adj
def tabu(adj, skip, rnd, iters=400000):
    m = len(adj); vs = [v for v in range(m) if v != skip]
    col = [rnd.randrange(K) for _ in range(m)]; col[skip] = -1
    gam = [[0] * K for _ in range(m)]
    for v in vs:
        for y in adj[v]:
            if y != skip: gam[v][col[y]] += 1
    tab = {}
    conf = sum(gam[v][col[v]] for v in vs) // 2
    for it in range(iters):
        if conf == 0: return col
        best = None; bd = 10**9
        cand = [v for v in vs if gam[v][col[v]] > 0]
        for v in cand:
            for c in range(K):
                if c == col[v]: continue
                d = gam[v][c] - gam[v][col[v]]
                if tab.get((v, c), -1) >= it and conf + d > 0: continue
                if d < bd or (d == bd and rnd.random() < 0.3): bd = d; best = (v, c)
        if best is None: continue
        v, c = best; o = col[v]; col[v] = c; conf += bd
        tab[(v, o)] = it + rnd.randrange(10) + int(0.6 * len(cand))
        for y in adj[v]:
            if y != skip: gam[y][o] -= 1; gam[y][c] += 1
    return None
def main():
    out, n, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); count = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    rnd = random.Random(seed)
    for i in range(count):
        for _ in range(1000):
            G = nx.random_regular_graph(D, n, seed=rnd.randrange(10**9))
            if nx.is_connected(G): break
        edges = [tuple(sorted(e)) for e in G.edges()]
        adj = l2(edges)
        top = 2 * D * (D - 1)
        hs = [v for v in range(len(edges)) if len(adj[v]) == top] or sorted(range(len(edges)), key=lambda v: -len(adj[v]))[:1]
        h = rnd.choice(hs)
        tag0 = f"K{K} n{n}"
        col = None
        for _ in range(5):
            col = tabu(adj, h, rnd)
            if col: break
        if col is None:
            print(tag0, "no colouring found", flush=True); continue
        tag = f"{out}/d{D}K{K}_n{n}_{seed}_{i}"
        with open(tag + ".in", "w") as f:
            f.write(f"{len(edges)} {h} {len(edges)}\n" + " ".join(map(str, col)) + "\n" + " ".join(map(str, range(len(edges)))) + "\n")
            for r in adj:
                f.write(f"{len(r)} " + " ".join(map(str, sorted(r))) + "\n")
        json.dump({"edges": edges, "e": h, "colouring": col, "instance": tag.rsplit('/', 1)[1]}, open(tag + ".json", "w"))
        print(tag, "m", len(edges), "deg h", len(adj[h]), "girth", nx.girth(G) if hasattr(nx, "girth") else "?", flush=True)
main()
