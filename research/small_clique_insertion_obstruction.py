"""Endpoint certificate: a B-K4 vertex need not be safe to insert into A.

This is a geometric local obstruction, NOT a globally optimal partition.
Standard-library only.  The selected A graph is O-v, and A+v is the
independently derived nine-vertex five-critical graph O.
"""
from itertools import combinations
import json
from pathlib import Path


def edge(a, b):
    return (min(a, b), max(a, b))


def adj(n, edges):
    out = [set() for _ in range(n)]
    for a, b in edges:
        assert a != b and b not in out[a]
        out[a].add(b)
        out[b].add(a)
    return out


def conflicts(ng, selected):
    out = [set() for _ in selected]
    for i, (a, b) in enumerate(selected):
        for j in range(i):
            c, d = selected[j]
            if {a, b} & {c, d} or any(y in ng[x] for x in (a, b) for y in (c, d)):
                out[i].add(j)
                out[j].add(i)
    return out


def girth_at_least_five(ng):
    seen = set()
    for v, ns in enumerate(ng):
        for u in ns:
            assert not (ns & ng[u]), ("triangle", v, u)
        for pair in combinations(sorted(ns), 2):
            assert pair not in seen, ("four_cycle", pair)
            seen.add(pair)


def colour(h, vertices, k):
    todo = set(vertices)
    colors = {}

    def search():
        if not todo:
            return dict(colors)
        v = max(todo, key=lambda x: (len({colors[u] for u in h[x] if u in colors}),
                                   len(h[x] & set(vertices)), -x))
        forbidden = {colors[u] for u in h[v] if u in colors}
        todo.remove(v)
        for c in range(k):
            if c not in forbidden:
                colors[v] = c
                result = search()
                if result is not None:
                    return result
        colors.pop(v, None)
        todo.add(v)
        return None

    result = search()
    if result is not None:
        assert all(result[u] != result[v] for u in vertices for v in h[u] if v in result)
    return result


def main():
    red = [(0, 6), (0, 7), (1, 8), (1, 9), (2, 10), (2, 11),
           (3, 12), (3, 13), (4, 5), (6, 14), (15, 16), (15, 17)]
    blue = [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (6, 15)]
    edges = list(map(lambda e: edge(*e), red + blue))
    ng = adj(18, edges)
    girth_at_least_five(ng)
    assert max(map(len, ng)) <= 4
    assert max(map(len, adj(18, red))) <= 2
    assert max(map(len, adj(18, blue))) <= 2
    h = conflicts(ng, red)
    expected_o = set(combinations(range(4), 2))
    expected_o |= set(combinations((0, 1, 4, 5), 2))
    expected_o |= set(combinations((2, 3, 6, 7), 2))
    expected_o |= {(4, 8), (5, 8), (6, 8), (7, 8)}
    assert {(u, v) for u in range(9) for v in h[u] if u < v < 9} == expected_o
    aa = set(range(1, 9))
    bb = {0, 9, 10, 11}
    assert all(v in h[u] for u, v in combinations(bb, 2))
    assert len(h[0] & aa) == 5
    assert max(len(h[v] & aa) for v in aa) == 4
    assert all(v in h[u] for u, v in combinations((2, 3, 6, 7), 2))
    assert not any(all(v in h[u] for u, v in combinations(q, 2))
                   for q in combinations(aa, 5))
    four = colour(h, aa, 4)
    assert four is not None
    assert colour(h, set(range(9)), 4) is None
    five = colour(h, set(range(9)), 5)
    assert five is not None

    # Balanced bipartite coloured completion.  Core edges have zero voltage;
    # missing red/blue slots are paired, with distinct voltages (t,t^2).
    # This is also directly checked below instead of relying only on the
    # voltage argument.
    left = {0, 3, 4, 8, 9, 10, 11, 14, 15}
    right = set(range(18)) - left
    assert all((a in left) != (b in left) for a, b in edges)
    added = []
    for kind, original in (("red", red), ("blue", blue)):
        nc = adj(18, original)
        ls = [v for v in sorted(left) for _ in range(2 - len(nc[v]))]
        rs = [v for v in sorted(right) for _ in range(2 - len(nc[v]))]
        assert len(ls) == len(rs)
        added.extend((kind, a, b) for a, b in zip(ls, rs))
    modulus = 23
    assert len(added) < modulus
    fiber = modulus * modulus
    vertex = lambda v, x, y: v * fiber + x * modulus + y
    all_edges, all_red = set(), set()

    def lift(kind, a, b, t):
        if a not in left:
            a, b = b, a
        for x in range(modulus):
            for y in range(modulus):
                e = edge(vertex(a, x, y),
                         vertex(b, (x + t) % modulus, (y + t * t) % modulus))
                assert e not in all_edges
                all_edges.add(e)
                if kind == "red":
                    all_red.add(e)

    for kind, original in (("red", red), ("blue", blue)):
        for a, b in original:
            lift(kind, a, b, 0)
    for t, (kind, a, b) in enumerate(added, 1):
        lift(kind, a, b, t)
    n = 18 * fiber
    gn, fn = adj(n, all_edges), adj(n, all_red)
    assert {len(x) for x in gn} == {4}
    assert {len(x) for x in fn} == {2}
    girth_at_least_five(gn)
    selected = [edge(vertex(a, 0, 0), vertex(b, 0, 0)) for a, b in red]
    assert conflicts(gn, selected) == h
    root = selected[0]
    root_conflicts = [e for e in all_red if e != root and
                      (set(e) & set(root) or any(y in gn[x] for x in root for y in e))]
    assert len(root_conflicts) == 12
    assert len(set(root_conflicts) - set(selected)) == 4

    result = {"status": "local geometric obstruction only; no global optimality asserted",
              "core_G_vertices": 18, "core_red": red, "core_blue": blue,
              "A_selected_indices": sorted(aa), "B_K4_selected_indices": sorted(bb),
              "root_index": 0, "A_four_coloring": four,
              "A_plus_root_five_coloring": five, "A_plus_root_not_four_colorable": True,
              "selected_H_edges": [(u, v) for u in range(12) for v in h[u] if u < v],
              "completion_modulus": modulus, "completion_added_base_edges": added,
              "completion_G_vertices": n, "completion_G_edges": len(all_edges),
              "completion_F_edges": len(all_red), "completion_four_regular": True,
              "completion_F_two_regular": True, "completion_girth_at_least_five": True,
              "root_degree": 12, "root_local_part_degrees": [5, 3, 4]}
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({"selected_vertices": 12, "A_chi": 4, "A_plus_root_chi": 5,
                      "completed_G_vertices": n, "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
