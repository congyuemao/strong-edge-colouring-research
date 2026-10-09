"""Finite local search for a subcubic 16-clique with a support boundary.

This is a targeted computation, not an integer coloring algorithm.  No graph
catalogue or external package is used.  The five-center reduction is derived
in clique16_boundary_model.md.  Output is explicitly a computational result.
"""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json
import argparse

TYPES = sorted((s for s in range(1, 32) if s.bit_count() <= 3),
               key=lambda s: (-s.bit_count(), s))


def multisets(caps, i=0, chosen=()):
    if not any(caps):
        yield chosen
        return
    if i == len(TYPES) or len(chosen) >= 9:
        return
    t = TYPES[i]
    inds = [j for j in range(5) if t >> j & 1]
    for count in range(min(caps[j] for j in inds) + 1):
        if len(chosen) + count > 9:
            break
        new = tuple(c - (count if j in inds else 0)
                    for j, c in enumerate(caps))
        yield from multisets(new, i + 1, chosen + (t,) * count)


def solve_case(qu, qv, counts, count_only=False):
    tu = (1 << qu) - 1
    tv = sum(1 << j for j in range(2, 2 + qv))
    caps = tuple(3 - int(bool((tu | tv) >> j & 1)) for j in range(5))
    locked = 31 ^ (tu | tv)
    for ts in multisets(caps):
        counts['incidence_multisets'] += 1
        if count_only:
            continue
        # Saturated centers cannot supply any missing cross-connection.
        # A forced D-D edge between overlapping Q types would be a Q triangle.
        alltypes = (tu, tv) + ts
        if any((s & t) and (s & ~t & locked) and (t & ~s & locked)
               for s, t in combinations(ts, 2)):
            counts['locked_overlap_reject'] += 1
            continue
        n = 7 + len(ts)
        adj = [0] * n
        q = [(5, 6)]

        def initial(u, v):
            adj[u] |= 1 << v
            adj[v] |= 1 << u

        initial(5, 6)
        for c in range(5):
            initial(c, 5 if c < 2 else 6)
        for x, t in enumerate(alltypes, 5):
            for c in range(5):
                if t >> c & 1:
                    initial(c, x)
                    q.append((c, x))
        assert len(q) == 16
        cap = [4] * n
        cap[5] = 3  # fourth u-neighbor is absent from the Q support
        if not valid(adj, q):
            counts['base_reject'] += 1
            continue
        counts['base_valid'] += 1
        answer = complete(adj, q, cap, counts)
        if answer is not None:
            return dict(qu=qu, qv=qv, types=ts, strong_clique=q,
                        edges=[(u, v) for u in range(n)
                               for v in range(u + 1, n) if answer[u] >> v & 1])
    return None


def clash(adj, e, f):
    a, b = e
    c, d = f
    return a in f or b in f or bool((adj[a] | adj[b]) & ((1 << c) | (1 << d)))


def valid(adj, q):
    for u, v in q:
        aa = adj[u] & ~(1 << v)
        bb = adj[v] & ~(1 << u)
        if aa & bb:  # no Q edge may lie on a triangle
            return False
        union = aa | bb
        internal = 0
        rest = union
        while rest:
            bit = rest & -rest
            rest ^= bit
            internal += (adj[bit.bit_length() - 1] & rest).bit_count()
        if internal > 4:  # necessary upper bound c_G <= 24 - internal
            return False
    # A common set of >=3 neighbors of 3 vertices is a K3,3 subgraph.
    return not any((adj[a] & adj[b] & adj[c]).bit_count() >= 3
                   for a, b, c in combinations(range(len(adj)), 3))


def complete(adj, q, cap, counts):
    counts['completion_nodes'] += 1
    best = None
    for e, f in combinations(q, 2):
        if clash(adj, e, f):
            continue
        opts = []
        for u in e:
            for v in f:
                if u in (5, 6) or v in (5, 6):
                    continue  # all within-support u,v neighbors are fixed
                if adj[u].bit_count() >= cap[u] or adj[v].bit_count() >= cap[v]:
                    continue
                trial = adj.copy()
                trial[u] |= 1 << v
                trial[v] |= 1 << u
                if valid(trial, q):
                    opts.append((u, v))
        if not opts:
            return None
        if best is None or len(opts) < len(best):
            best = opts
    if best is None:
        return adj
    for u, v in best:
        trial = adj.copy()
        trial[u] |= 1 << v
        trial[v] |= 1 << u
        answer = complete(trial, q, cap, counts)
        if answer is not None:
            return answer
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--count-only', action='store_true')
    parser.add_argument('--qu', type=int, choices=(0, 1, 2))
    parser.add_argument('--qv', type=int, choices=(0, 1, 2))
    args = parser.parse_args()
    allresults = []
    for qu in ((args.qu,) if args.qu is not None else (0, 1, 2)):
        for qv in ((args.qv,) if args.qv is not None else (0, 1, 2)):
            counts = Counter()
            answer = solve_case(qu, qv, counts, args.count_only)
            result = dict(qu=qu, qv=qv, counts=dict(counts), found=answer)
            print(json.dumps(result), flush=True)
            allresults.append(result)
    Path('research/clique16_boundary_result.json').write_text(
        json.dumps(allresults, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
