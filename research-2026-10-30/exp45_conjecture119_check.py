"""exp45: check the end states of exp38's GMODE 12 / 13 attacks on conjecture 11.9 (NEW_DIRECTIONS 11.16).

For the best state of every edge of each run: is e depth-1 stuck; how many pairs (a, b), a, b != p, are separable at
each singleton member f_p, counted twice (exp38's singleton_pairs, which uses exp33's code, and an independent count
built from the vertex incidences); the KIL2 margin (most pairs opened at e by one first move).

Usage (run from this directory): exp45_conjecture119_check.py <exp38 outdir> ...
Result (2026-11-03, D:/se20-data/runs/gpu_plan8): the two counts agree on all 56 end states; see NEW_DIRECTIONS 11.16.
"""
import json
import sys
from collections import defaultdict

import numpy as np
from exp38_gpu_adversary import build_instances, parse_specs, from_bits, classify, proper, singleton_pairs, good_first_moves

K = 20


def indep_counts(edges, e, col):
    inc = defaultdict(set)
    for i, (u, v) in enumerate(edges):
        inc[u].add(i)
        inc[v].add(i)
    N = {}
    def nbr(h):
        if h not in N:
            u, v = edges[h]
            near = inc[u] | inc[v]
            out = set(near)
            for g in near:
                out |= inc[edges[g][0]] | inc[edges[g][1]]
            out.discard(h)
            N[h] = out
        return N[h]
    res = {}
    for p in range(K):
        mem = [f for f in nbr(e) if col[f] == p]
        if len(mem) != 1:
            continue
        Nf, s = nbr(mem[0]), 0
        for a in range(K):
            for b in range(a + 1, K):
                if p in (a, b):
                    continue
                Bset, seen, ok = {g for g in Nf if col[g] == b}, set(), True
                for st in (g for g in Nf if col[g] == a):
                    if st in seen:
                        continue
                    comp, stack = {st}, [st]
                    while stack:
                        x = stack.pop()
                        for y in nbr(x):
                            if y not in comp and col[y] in (a, b):
                                comp.add(y)
                                stack.append(y)
                    seen |= comp
                    if comp & Bset:
                        ok = False
                        break
                s += ok
        res[p] = s
    return res


for d in sys.argv[1:]:
    meta = json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]
    xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
    with np.load(f"{d}/state.npz") as st:
        b, bc = st["bestEs"], st["bcls"]
    rows, bad = [], 0
    for i, x in enumerate(xs):
        c = i * per + int(np.argmin(b[i * per:(i + 1) * per]))
        col = from_bits(bc[c], len(x["adj"]))
        stuck = proper(x["adj"], col, x["e"]) and sum(classify(x["adj"], col, x["e"])) == 0 \
            and len({col[f] for f in x["adj"][x["e"]]}) == K
        sp, ic = singleton_pairs(x["adj"], list(col), x["e"]), indep_counts(x["edges"], x["e"], col)
        bad += sp != ic
        v = sorted(sp.values())
        kil2 = good_first_moves(x["adj"], list(col), x["e"], smax=0)
        rows.append((int(b[c]), stuck, len(v), v[0], v[-1], sum(v) / len(v), kil2))
    print(d.rsplit("/", 1)[1], f"{len(rows)} end states, independent count differs on {bad}")
    print("  all stuck at e:", all(r[1] for r in rows), "; singletons per state:", sorted({r[2] for r in rows}))
    print("  energy, fewest / most / mean pairs over singleton members, KIL2 margin:")
    for r in sorted(rows):
        print(f"    E={r[0]:3d}  min {r[3]:3d}  max {r[4]:3d}  mean {r[5]:5.1f}  kil2 {r[6]}")
