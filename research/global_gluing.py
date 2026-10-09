"""Construct and independently check the small-cut gluing arguments.

Python standard library only. These finite checks supplement, not replace,
the proofs in global_continuation.md.
"""
from itertools import combinations
from pathlib import Path
import json
from structural_factors import conflicts, exact_colouring


def edge(u, v):
    return tuple(sorted((u, v)))


def adjacency(edges):
    out = {}
    for u, v in edges:
        out.setdefault(u, set()).add(v)
        out.setdefault(v, set()).add(u)
    return out


def verify(edges, colours, k):
    assert len(edges) == len(set(edges)) == len(colours)
    adj = adjacency(edges)
    assert max(map(len, adj.values()), default=0) <= 4
    assert all(0 <= colours[e] < k for e in edges)
    # Independent direct endpoint definition, not the matrix used to glue.
    for (u, v), (x, y) in combinations(edges, 2):
        conflict = (len({u, v, x, y}) < 4 or x in adj[u] or y in adj[u]
                    or x in adj[v] or y in adj[v])
        assert not conflict or colours[edge(u, v)] != colours[edge(x, y)]


def initial_colouring(edges, k, shift=0):
    n = max((max(e) for e in edges), default=-1) + 1
    _, colours, _ = exact_colouring(conflicts(n, edges, edges))
    answer = {e: (c + shift) % k for e, c in zip(edges, colours)}
    verify(edges, answer, k)
    return answer


def star(edges, colours, v):
    return {colours[e] for e in edges if v in e}


def near(edges, colours, v):
    adj = adjacency(edges)
    vertices = adj.get(v, set()) | {v}
    return {colours[e] for e in edges if vertices & set(e)}


def permutation(k, banned, prescribed):
    assert len(set(prescribed.values())) == len(prescribed)
    assert all(y not in banned[x] for x, y in prescribed.items())
    fixed_targets = set(prescribed.values())
    owner = {y: x for x, y in prescribed.items()}

    def augment(x, seen):
        for y in range(k):
            if y in fixed_targets or y in banned[x] or y in seen:
                continue
            seen.add(y)
            if y not in owner or augment(owner[y], seen):
                owner[y] = x
                return True
        return False

    for x in range(k):
        if x not in prescribed:
            assert augment(x, set()), (k, banned, prescribed)
    return {x: y for y, x in owner.items()}


def glue_edge_cut(ea, ca, eb, cb, cut, k=20):
    """cut contains ordered pairs (A endpoint, B endpoint)."""
    assert len(cut) in (1, 2, 3, 4)
    a = [u for u, _ in cut]
    b = [v for _, v in cut]
    if len(cut) == 3:
        assert len(set(a)) >= 2 and len(set(b)) >= 2
        # Put the repeated side in B when just A has type 2+1.
        if len(set(a)) == 2 and len(set(b)) == 3:
            return glue_edge_cut(eb, cb, ea, ca, [(v, u) for u, v in cut], k)
    if len(cut) == 4:
        assert max(a.count(u) for u in a) <= 2
        assert max(b.count(v) for v in b) <= 2
        if len(set(a)) < 4 and len(set(b)) == 4:
            return glue_edge_cut(eb, cb, ea, ca, [(v, u) for u, v in cut], k)
    sa = [star(ea, ca, u) for u in a]
    sb = [star(eb, cb, v) for v in b]
    ta = [near(ea, ca, u) for u in a]
    tb = [near(eb, cb, v) for v in b]
    ua, ub = set().union(*sa), set().union(*sb)
    banned = [set() for _ in range(k)]
    for left, right in zip(sa, sb):
        for x in right:
            banned[x] |= left
    palette = set(range(k))
    prescribed = {}
    targets = []
    if len(cut) <= 2:
        assert k >= (13 if len(cut) == 1 else 17)
        for i in range(len(cut)):
            target_free = palette - (ta[i] | ua) - set(targets)
            source_free = palette - (tb[i] | ub) - set(prescribed)
            assert target_free and source_free
            alpha, x = min(target_free), min(source_free)
            prescribed[x] = alpha
            targets.append(alpha)
    elif len(set(b)) < len(cut):
        source_lists = [palette - (tb[i] | ub) for i in range(len(cut))]
        sources = {}
        for i in sorted(range(len(cut)), key=lambda i: len(source_lists[i])):
            sources[i] = min(source_lists[i] - set(sources.values()))
        for i in range(len(cut)):
            actual_a = ta[i] | set().union(*(sa[j] for j in range(len(cut)) if b[j] == b[i]))
            target_free = palette - actual_a - set(targets)
            assert target_free
            x, alpha = sources[i], min(target_free)
            prescribed[x] = alpha
            targets.append(alpha)
    else:
        assert len(set(a)) == len(set(b)) == len(cut)
        for i in range(len(cut)):
            multiple = {c for c in palette if sum(c in sb[j] for j in range(len(cut)) if j != i) >= 2}
            source_free = palette - tb[i] - multiple - set(prescribed)
            assert source_free
            x = min(source_free)
            target_free = palette - ta[i] - banned[x] - set(targets)
            assert target_free
            alpha = min(target_free)
            prescribed[x] = alpha
            targets.append(alpha)
    pi = permutation(k, banned, prescribed)
    result = dict(ca)
    result.update({e: pi[c] for e, c in cb.items()})
    result.update({edge(*e): c for e, c in zip(cut, targets)})
    all_edges = sorted(ea + eb + [edge(*e) for e in cut])
    verify(all_edges, result, k)
    return all_edges, result


def glue_vertex_cut(ea, ca, eb, cb, separator, k=20):
    assert k == 20
    assert not set(ea) & set(eb)
    assert not any(set(e) <= set(separator) for e in ea + eb)
    assert sum(bool(set(e) & set(separator)) for e in ea) <= 4
    assert sum(bool(set(e) & set(separator)) for e in eb) <= 4
    adj = adjacency(ea + eb)
    banned = [set() for _ in range(k)]
    for u, v in ea:
        for x, y in eb:
            if (len({u, v, x, y}) < 4 or x in adj[u] or y in adj[u]
                    or x in adj[v] or y in adj[v]):
                banned[cb[edge(x, y)]].add(ca[edge(u, v)])
    assert all(len(row) <= 16 for row in banned)
    assert all(sum(y in row for row in banned) <= 16 for y in range(k))
    pi = permutation(k, banned, {})
    result = dict(ca)
    result.update({e: pi[c] for e, c in cb.items()})
    all_edges = sorted(ea + eb)
    verify(all_edges, result, k)
    return all_edges, result


def complete(vertices):
    return sorted(combinations(vertices, 2))


if __name__ == '__main__':
    cases = []

    def record(name, ea, eb, cut=None, separator=None, k=20):
        # Vary the source palette deliberately; gluing cannot assume aligned
        # colours or the freedom to recolour either side internally.
        for shift in range(k):
            ca = initial_colouring(ea, k)
            cb = initial_colouring(eb, k, shift)
            if cut is not None:
                edges, colours = glue_edge_cut(ea, ca, eb, cb, cut, k)
            else:
                edges, colours = glue_vertex_cut(ea, ca, eb, cb, separator, k)
            cases.append(dict(name=name, shift=shift, k=k, edges=edges,
                              colours=[colours[e] for e in edges]))

    a = [e for e in complete(range(5)) if e != (0, 1)]
    b = [e for e in complete(range(5, 10)) if e != (5, 6)]
    record('one_cut', a, b, cut=[(0, 5)], k=13)
    record('two_cut_distinct', a, b, cut=[(0, 5), (1, 6)], k=17)
    a_shared = [e for e in complete(range(5)) if e not in ((0, 1), (0, 2))]
    record('two_cut_shared', a_shared, b, cut=[(0, 5), (0, 6)], k=17)

    a = complete(range(4))
    b = complete(range(4, 8))
    record('three_cut_distinct', a, b, cut=[(0, 4), (1, 5), (2, 6)])
    b_shared = [e for e in b if e != (4, 5)]
    record('three_cut_one_repeated_side', a, b_shared,
           cut=[(0, 4), (1, 4), (2, 5)])
    a_shared = [e for e in a if e != (0, 1)]
    record('three_cut_both_repeated_sides', a_shared, b_shared,
           cut=[(0, 4), (0, 5), (1, 5)])

    record('four_cut_distinct', a, b, cut=[(0, 4), (1, 5), (2, 6), (3, 7)])
    record('four_cut_1111_211', a, b_shared, cut=[(0, 4), (1, 4), (2, 6), (3, 7)])
    record('four_cut_1111_22', a, b_shared, cut=[(0, 4), (1, 4), (2, 5), (3, 5)])
    record('four_cut_211_211', a_shared, b_shared, cut=[(0, 4), (0, 6), (2, 4), (3, 7)])
    record('four_cut_22_211', a_shared, b_shared, cut=[(0, 4), (0, 6), (1, 4), (1, 7)])
    record('four_cut_22_22', a_shared, b_shared, cut=[(0, 4), (0, 5), (1, 4), (1, 5)])

    for left_count in (1, 2, 3):
        a = complete(range(4)) + [edge(i, 8 if i < left_count else 9) for i in range(4)]
        b = complete(range(4, 8)) + [edge(i, 8 if i-4 < 4-left_count else 9) for i in range(4, 8)]
        record('vertex_cut_' + str(left_count), sorted(a), sorted(b), separator=(8, 9))

    out = Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(cases, indent=2), encoding='utf-8')
    print('Verified', len(cases), 'glued colourings with direct original-edge checks.')
