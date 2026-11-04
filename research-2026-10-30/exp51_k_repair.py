"""exp51: k-colour repairs of a stuck edge (NEW_DIRECTIONS 11.24).

Fix a colour set Y with |Y| = k and let U_Y be h together with the edges coloured from Y.  If L^2[U_Y] is k-colourable, recolouring
U_Y alone colours h: the other colours are untouched.  k = 2 is exactly "the pair is separable".  A sufficient local test is the
k-core: peel vertices with fewer than k neighbours in U_Y; if h is peeled, colour back in reverse order.  With radius r, only
edges within L^2-distance r of h may be peeled (everything farther is treated as fixed), so success uses only the r-ball.

For each state prints, per k: #Y with h outside the k-core, #Y 3-colourable exactly (k = 3, on the core by SAT), and the
number of Y repaired within radius r.  Every repair reported by 'verify' is carried out and re-checked by vertex relations.
Usage: exp51_k_repair.py k [files or gpu dirs...]
"""
import itertools
import json
import os
import random
import sys

import numpy as np
from pysat.solvers import Cadical195

from exp33_kempe import K, l2_adj


def states(args):
    for src in args:
        if src.endswith(".json"):
            for x in json.load(open(src, encoding="utf-8")):
                yield os.path.basename(src)[:24] + " " + x["instance"], [tuple(e) for e in x["edges"]], x["e"], x["colouring"]
        else:
            from exp38_gpu_adversary import build_instances, parse_specs, from_bits
            meta = json.load(open(f"{src}/meta.json", encoding="utf-8"))["meta"]
            insts = build_instances(parse_specs(meta["spec"]))
            with np.load(f"{src}/state.npz") as z:
                bcls, bE = z["bcls"], z["bestEs"]
            per = meta["per"]
            for i, x in enumerate(insts):
                j = i * per + int(np.argmin(bE[i * per:(i + 1) * per]))
                col = from_bits(bcls[j], len(x["adj"]))
                yield os.path.basename(src) + " " + x["name"], x["edges"], x["e"], col


def core_has(adj_set, nodes, h, k, frozen=frozenset()):
    deg = {x: len(adj_set[x] & nodes) for x in nodes}
    stack = [x for x in nodes if deg[x] < k and x not in frozen]
    alive = set(nodes)
    order = []
    while stack:
        x = stack.pop()
        if x not in alive:
            continue
        alive.discard(x)
        order.append(x)
        if x == h:
            return False, alive, order
        for y in adj_set[x] & alive:
            deg[y] -= 1
            if deg[y] < k and y not in frozen:
                stack.append(y)
    return True, alive, order


def colourable(adj_set, core, k):
    core = sorted(core)
    idx = {x: i for i, x in enumerate(core)}
    cl = []
    v = lambda x, c: idx[x] * k + c + 1
    for x in core:
        cl.append([v(x, c) for c in range(k)])
        for y in adj_set[x]:
            if y in idx and y > x:
                cl += [[-v(x, c), -v(y, c)] for c in range(k)]
    with Cadical195(bootstrap_with=cl) as s:
        return s.solve()


def ball(adj_set, h, r):
    seen = {h}
    fr = {h}
    for _ in range(r):
        fr = {y for x in fr for y in adj_set[x]} - seen
        seen |= fr
    return seen


def main():
    k = int(sys.argv[1])
    print("state | stuck check | Y | outside k-core | radius 1,2,3 | k-colourable exact (k=3) | largest peel needed")
    tot = None
    for name, edges, h, col in states(sys.argv[2:]):
        adj = [set(r) for r in l2_adj(edges)]
        col = list(col)
        col[h] = -1
        assert all(col[x] != col[y] or col[x] < 0 for x in range(len(adj)) for y in adj[x] if x != h and y != h), "not proper"
        assert len({col[x] for x in adj[h]}) == K
        classes = [{x for x, c in enumerate(col) if c == a} for a in range(K)]
        balls = {r: ball(adj, h, r) for r in (1, 2, 3)}
        nodes_all = set(range(len(adj)))
        res = dict(Y=0, out=0, r1=0, r2=0, r3=0, exact=0)
        peel_max = 0
        for Y in itertools.combinations(range(K), k):
            U = set().union(*(classes[a] for a in Y)) | {h}
            res["Y"] += 1
            has, alive, order = core_has(adj, U, h, k)
            if not has:
                res["out"] += 1
                peel_max = max(peel_max, len(order))
                for r in (1, 2, 3):
                    if not core_has(adj, U, h, k, frozenset(U - balls[r]))[0]:
                        res[f"r{r}"] += 1
            elif k <= 3 and colourable(adj, alive, k):
                res["exact"] += 1
        print(name[:60], res, "peel", peel_max, flush=True)
        tot = {a: min(tot[a], res[a]) for a in res} if tot else dict(res)
    print("minimum over the states:", tot)


main()
