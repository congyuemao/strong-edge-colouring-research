"""Decode an exp15 witness: how is each parity detour blocked?"""
import collections
import sys

from exp14_periodic import PState
from exp15_phi2first import build, detours, deg

pattern, L, D, opts = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), set(sys.argv[4].split(","))
M = build(pattern, L, D, opts)
assert M.s.solve()
mod = set(l for l in M.s.get_model() if l > 0)
val = lambda l: (l in mod) if l > 0 else (-l not in mod)
cls = lambda e: next(c for c in range(M.K) if val(M.x[e, c]))
cyc = [e for e in M.base_edges(1) if M.in_cycle(e)]
reasons = collections.Counter()
for seg, W in detours(M, cyc):
    why = set()
    for w in W:
        q0 = [n for n in M.nbrs(w) if not M.in_cycle(n) and n not in W and cls(n) == 0]
        if q0:
            why.add(f"W-edge has extra class-0 nbr(s) x{len(q0)}")
    if not why:
        # blocked only through destinations of the segment edges
        why.add("segment edges have no free destination")
    reasons[(len(seg), len(W), tuple(sorted(why)))] += 1
for k, v in sorted(reasons.items()):
    print(v, k)
# how many non-cycle class-0 edges sit next to the cycle?
near0 = [n for e in cyc for n in M.nbrs(e) for z in M.nbrs(n) if not M.in_cycle(z) and cls(z) == 0]
print("class-0 non-cycle edges within distance 2 of the cycle (with mult.):", len(near0))
for e in cyc:
    print("cycle edge", e, "class degrees:", [sum(1 for n in M.nbrs(e) if cls(n) == c) for c in range(M.K)])
