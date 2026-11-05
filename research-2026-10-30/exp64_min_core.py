"""exp64: how small can a set C containing h be, if every edge of C has at least 14 neighbours in C (the weakest core of k = 2, d_ab = 2)?  Upper bound by randomised peeling: remove a random edge, cascade, keep if h survives.
A density well above the tangling budget would give a global contradiction on that graph.  Usage: exp64_min_core.py tau seconds files.json"""
import json, random, sys, time
from exp33_kempe import l2_adj
tau = int(sys.argv[1]); secs = float(sys.argv[2])
def peel(adj, C, x, h, tau, cnt):
    C = set(C); cnt = dict(cnt); st = [x]; C.discard(x)
    while st:
        v = st.pop()
        if v == h: return None, None
        for y in adj[v]:
            if y in C:
                cnt[y] -= 1
                if cnt[y] < tau:
                    C.discard(y); st.append(y)
    return C, cnt
for f in sys.argv[3:]:
    for x in json.load(open(f)):
        edges = [tuple(e) for e in x["edges"]]; h = x["e"]; adj = [set(r) for r in l2_adj(edges)]; m = len(edges)
        C0 = set(range(m)); cnt0 = {v: len(adj[v]) for v in C0}
        best = m; rng = random.Random(1); t0 = time.time(); bestC = None
        while time.time() - t0 < secs:
            C, cnt = set(C0), dict(cnt0)
            while True:
                cand = list(C - {h}); rng.shuffle(cand); moved = False
                for y in cand[:40]:
                    if y not in C: continue
                    C2, c2 = peel(adj, C, y, h, tau, cnt)
                    if C2 is not None and len(C) - len(C2) <= 6 + rng.randrange(6):
                        C, cnt = C2, c2; moved = True; break
                if not moved: break
            if len(C) < best: best = len(C); bestC = set(C)
        nb = {}
        for i in bestC:
            for v in edges[i]: nb[v] = nb.get(v, 0) + 1
        hist = [sum(1 for v in nb.values() if v == d) for d in range(1, 5)]
        print(f"{x.get('instance','?')[:22]} m={m} tau={tau}: smallest core found {best}, density {best/m:.3f}; vertex degrees in C (1,2,3,4) {hist}", flush=True)
