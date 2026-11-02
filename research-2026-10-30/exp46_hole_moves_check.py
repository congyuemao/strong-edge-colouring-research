"""exp46: numerical checks for the lemmas of NEW_DIRECTIONS 11.17 (the attempt at a positive proof of conjecture 11.9),
on the end states of exp38 runs (the best state of every edge, all depth-1 stuck at e).

  11.12  move the hole from e to a singleton member f_p (e gets p, f_p is uncoloured): no pair (p, x) is separable
         at f_p;
  11.13  pairs (a, b) at f_p whose singleton members f_a, f_b of N(e) both conflict with f_p are not separable;
         how many such inherited pairs a near / far f_p has, and whether the f_p with the fewest separable pairs
         (outside p) is a near edge;
  11.14  every colour c that appears at least twice on N(e): the pairs (a, b), c not in {a, b}, separable at the
         whole c-class jointly; for up to 3 of them per colour the repair is carried out (swap, recolour every
         c-member to a, colour e with c) and checked with conflict code built from the vertex incidences only.

Usage (run from this directory): exp46_hole_moves_check.py <exp38 outdir> ...
Result (2026-11-03, D:/se20-data/runs/gpu_plan8, 80 end states): see NEW_DIRECTIONS 11.17.
"""
import json
import sys
from collections import Counter, defaultdict

import numpy as np
from exp38_gpu_adversary import build_instances, parse_specs, from_bits, classify
from exp33_kempe import separable, component

K = 20


def proper_vertex(edges, col):
    """Strong-colouring check from the vertex incidences only (uncoloured edges are -1)."""
    inc = defaultdict(list)
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)
    for i, (u, v) in enumerate(edges):
        if col[i] < 0:
            continue
        near = set(inc[u]) | set(inc[v])
        for g in list(near):
            near |= set(inc[edges[g][0]]) | set(inc[edges[g][1]])
        near.discard(i)
        if any(col[g] == col[i] for g in near):
            return False
    return True


def class_separable(adj, col, members, a, b):
    """Components to swap if no (a, b)-component meets both an a-neighbour and a b-neighbour of the members, else None."""
    A = {g for m in members for g in adj[m] if col[g] == a}
    B = {g for m in members for g in adj[m] if col[g] == b}
    comps, seen = [], set()
    for s in A:
        if s in seen:
            continue
        comp = component(adj, col, s, a, b)
        if B & set(comp):
            return None
        seen |= set(comp)
        comps.append(comp)
    return comps


def pairs_at(adj, col, f, p):
    return sum(separable(adj, col, f, a, b) is not None for a in range(K) for b in range(a + 1, K) if p not in (a, b))


tot = Counter()
for d in sys.argv[1:]:
    meta = json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]
    xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
    with np.load(f"{d}/state.npz") as st:
        bE, bc = st["bestEs"], st["bcls"]
    inh, cls, weakest_near, reps = defaultdict(list), [], 0, 0
    for i, x in enumerate(xs):
        adj, e, edges = x["adj"], x["e"], x["edges"]
        c = i * per + int(np.argmin(bE[i * per:(i + 1) * per]))
        col = list(from_bits(bc[c], len(adj)))
        assert sum(classify(adj, col, e)) == 0 and len({col[f] for f in adj[e]}) == K, "not stuck at e"
        mult = Counter(col[f] for f in adj[e])
        single = {q: next(f for f in adj[e] if col[f] == q) for q in range(K) if mult[q] == 1}
        counts = []
        for p, fp in single.items():
            moved = list(col)
            moved[e], moved[fp] = p, -1
            tot["11.12 pairs (p, x) checked"] += K - 1
            tot["11.12 separable (should be 0)"] += sum(separable(adj, moved, fp, p, q) is not None
                                                        for q in range(K) if q != p)
            near = bool(set(edges[fp]) & set(edges[e]))
            I = [(a, b) for a in single for b in single if a < b and p not in (a, b)
                 and single[a] in adj[fp] and single[b] in adj[fp]]
            tot["11.13 inherited pairs checked"] += len(I)
            tot["11.13 separable (should be 0)"] += sum(separable(adj, col, fp, a, b) is not None for a, b in I)
            inh["near" if near else "far"].append(len(I))
            counts.append((pairs_at(adj, col, fp, p), near))
        weakest_near += min(counts)[1]
        for cc in (q for q in range(K) if mult[q] >= 2):
            mem = [f for f in adj[e] if col[f] == cc]
            ok = [(a, b) for a in range(K) for b in range(a + 1, K) if cc not in (a, b)
                  and class_separable(adj, col, mem, a, b) is not None]
            cls.append(len(ok))
            for a, b in ok[:3]:
                rep = list(col)
                for comp in class_separable(adj, rep, mem, a, b):
                    for h in comp:
                        rep[h] = b if rep[h] == a else a
                for m in mem:
                    rep[m] = a
                rep[e] = cc
                reps += 1
                tot["11.14 repairs illegal (should be 0)"] += not proper_vertex(edges, rep)
    tot["end states"] += len(xs)
    tot["11.14 repairs"] += reps
    print(f"{d}: {len(xs)} end states; the weakest f_p is near in {weakest_near}; inherited pairs near "
          f"{min(inh['near'])}-{max(inh['near'])}, far {min(inh['far'])}-{max(inh['far'])}; {len(cls)} colours "
          f"appearing at least twice, {min(cls)}-{max(cls)} pairs separable at the class ({cls.count(0)} with none); "
          f"{reps} repairs carried out", flush=True)
print(dict(tot))
