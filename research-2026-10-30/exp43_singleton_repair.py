"""exp43: insertion through a singleton member (NEW_DIRECTIONS 11.14, theorem 11.7), checked on stuck states.

Theorem 11.7: e blocked, p a colour with a single member f_p on N(e), (a, b) a pair with a, b != p that is separable AT
f_p (no (a, b)-component holds both an a- and a b-neighbour of f_p).  Swap the (a, b)-components of the a-neighbours of
f_p, recolour f_p to a, colour e with p: the result is a proper strong colouring with e coloured.

Chains (theorem 11.7 for k = 2): alpha is the only a-coloured neighbour of f_p and (c, d), c, d not in {p, a}, is
separable at alpha.  Swap the (c, d)-components of the c-neighbours of alpha, recolour alpha to c, f_p to a, colour e
with p.

Per state: how many singleton members f_p have such a pair (are not depth-1 stuck at f_p), how many pairs each, and
for up to 3 pairs per f_p the repair is carried out and the whole colouring re-checked by independent code (conflicts
from the vertex sets); the same check for up to 4 chains of length 2 per state.  Sources as in exp42 (repo, hunt:<dir>:<k>, npz:<dir>).
Usage (run from this directory): exp43_singleton_repair.py <out.jsonl> <workers> <source> ...
"""
import json
import random
import sys
from collections import Counter
from multiprocessing import Pool

from exp33_kempe import K, l2_adj, separable, swap
from exp42_first_move_shapes import states


def proper(edges, col):
    """Independent check from the vertex sets: two edges conflict iff they share a vertex or an edge joins them."""
    nb = {}
    for x, y in edges:
        nb.setdefault(x, set()).add(y)
        nb.setdefault(y, set()).add(x)
    by = {}
    for i, c in enumerate(col):
        if c >= 0:
            by.setdefault(c, []).append(i)
    for c, es in by.items():
        verts = Counter()
        for i in es:
            for v in edges[i]:
                verts[v] += 1
        if max(verts.values()) > 1:
            return False
        for i in es:                                  # an edge joining two c-edges
            x, y = edges[i]
            for j in es:
                if j <= i:
                    continue
                u, w = edges[j]
                if any(t in nb[s] for s in (x, y) for t in (u, w)):
                    return False
    return True


def run(job):
    src, edges, e, col = job
    adj, col = l2_adj(edges), list(col)
    Ne = adj[e]
    mult = Counter(col[f] for f in Ne)
    good_p, checked, ok = [], 0, 0
    for p in [c for c in range(K) if mult[c] == 1]:
        fp = next(f for f in Ne if col[f] == p)
        pairs = []
        for a in range(K):
            for b in range(a + 1, K):
                if p in (a, b):
                    continue
                for x, y in ((a, b), (b, a)):
                    comps = separable(adj, col, fp, x, y)
                    if comps is not None and any(col[g] == x for g in adj[fp]):
                        pairs.append((x, y, comps))
                        break
        if pairs:
            good_p.append((p, len(pairs)))
            for x, y, comps in pairs[:3]:                 # carry out the repair and check it
                c2 = list(col)
                for comp in comps:
                    swap(c2, comp, x, y)
                assert not any(c2[g] == x for g in adj[fp])
                c2[fp] = x
                c2[e] = p
                checked += 1
                ok += proper(edges, c2) and all(c >= 0 for c in c2)
    c2_checked = c2_ok = 0
    for p in [c for c in range(K) if mult[c] == 1][:2]:      # chains e, f_p, alpha
        fp = next(f for f in Ne if col[f] == p)
        around = Counter(col[g] for g in adj[fp] if col[g] >= 0)
        for a in [c for c in range(K) if around[c] == 1][:2]:
            al = next(g for g in adj[fp] if col[g] == a)
            found = None
            for c in range(K):
                for d in range(K):
                    if c != d and not {c, d} & {p, a} and found is None:
                        comps = separable(adj, col, al, c, d)
                        if comps is not None:
                            found = (c, d, comps)
            if found is None:
                continue
            c, d, comps = found
            c2 = list(col)
            for comp in comps:
                swap(c2, comp, c, d)
            c2[al], c2[fp], c2[e] = c, a, p
            c2_checked += 1
            c2_ok += proper(edges, c2) and all(x >= 0 for x in c2)
    return {"src": src, "singletons": sum(v == 1 for v in mult.values()), "non_stuck_singletons": len(good_p),
            "pairs_per_singleton": sorted(n for _, n in good_p), "repairs_checked": checked, "repairs_ok": ok,
            "chain2_checked": c2_checked, "chain2_ok": c2_ok}


if __name__ == "__main__":
    jobs = list(states(sys.argv[3:], random.Random(1)))
    with Pool(int(sys.argv[2])) as pool, open(sys.argv[1], "w", encoding="utf-8", newline="\n") as fh:
        for r in pool.imap_unordered(run, jobs):
            fh.write(json.dumps(r) + "\n")
    R = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
    print(len(R), "states; repairs checked", sum(r["repairs_checked"] for r in R), "ok", sum(r["repairs_ok"] for r in R),
          "; length-2 chains checked", sum(r["chain2_checked"] for r in R), "ok", sum(r["chain2_ok"] for r in R))
    print("non-stuck singleton members per state:", sorted(Counter(r["non_stuck_singletons"] for r in R).items()))
    print("states with none:", sum(r["non_stuck_singletons"] == 0 for r in R))
    for r in sorted(R, key=lambda r: r["non_stuck_singletons"])[:5]:
        print(r["src"][:60], r["non_stuck_singletons"], "of", r["singletons"], r["pairs_per_singleton"])
