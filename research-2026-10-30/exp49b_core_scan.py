"""exp49b: for every connected 4-regular graph on n vertices: the 20-core of L^2 (peel edges of degree <= 19), d + omega
inside the core, and the largest clique of L^2 whose members all have degree >= 20 in L^2 (NEW_DIRECTIONS 11.21).
Usage: exp49b_core_scan.py n1,n2,...
"""
import sys
from collections import Counter
from multiprocessing import Pool

def l2(edges):
    m = len(edges)
    nb = {}
    for u, v in edges:
        nb.setdefault(u, set()).add(v); nb.setdefault(v, set()).add(u)
    adj = [0] * m
    for i in range(m):
        a, b = edges[i]
        Wi = nb[a] | nb[b]
        for j in range(i + 1, m):
            c, d = edges[j]
            if c in Wi or d in Wi:
                adj[i] |= 1 << j; adj[j] |= 1 << i
    return adj

def max_clique(adj, cand):
    """size of a largest clique inside bitset cand (Tomita style with a simple greedy colour bound)"""
    best = 0
    def expand(P, size):
        nonlocal best
        while P:
            if size + bin(P).count("1") <= best:
                return
            # greedy colour bound
            colours, Q, order = 0, P, []
            while Q:
                colours += 1
                R = Q
                while R:
                    v = (R & -R).bit_length() - 1
                    R &= ~(1 << v) & ~adj[v]
                    Q &= ~(1 << v)
                    order.append((v, colours))
            for v, c in reversed(order):
                if size + c <= best:
                    return
                expand(P & adj[v], size + 1) if P & adj[v] else None
                if size + 1 > best:
                    best = size + 1
                P &= ~(1 << v)
            return
    expand(cand, 0)
    return best

def job(args):
    gi, edges = args
    adj = l2(edges)
    m = len(edges)
    deg = [bin(a).count("1") for a in adj]
    core = (1 << m) - 1
    changed = True
    while changed:
        changed = False
        c = core
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            if bin(adj[v] & core).count("1") <= 19:
                core &= ~(1 << v); changed = True
    high = sum(1 << i for i in range(m) if deg[i] >= 20)
    om_high = max_clique(adj, high) if high else 0
    cs = bin(core).count("1")
    worst = 0
    if core:
        c = core
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            d = bin(adj[v] & core).count("1")
            w = 1 + max_clique(adj, adj[v] & core) if adj[v] & core else 1
            worst = max(worst, d + w)
    return gi, cs, worst, om_high, m

if __name__ == "__main__":
    from exp33_kempe import load
    for n in map(int, sys.argv[1].split(",")):
        jobs = list(enumerate(load(n)))
        cs, ws, oh = Counter(), Counter(), Counter()
        ex = {}
        with Pool(6) as pool:
            for gi, c, w, o, m in pool.imap_unordered(job, jobs, chunksize=50):
                cs["empty" if c == 0 else ("all" if c == m else "part")] += 1
                ws[w] += 1
                oh[o] += 1
                ex.setdefault(("w", w), gi); ex.setdefault(("o", o), gi)
        print(f"n={n}: {len(jobs)} graphs; core {dict(cs)}; max(d+omega) in core {dict(sorted(ws.items()))}; largest clique of edges with L2 degree >= 20: {dict(sorted(oh.items()))}; examples {[(k, v) for k, v in ex.items() if k[1] >= 13 or (k[0]=='w' and k[1]>=36)]}", flush=True)
