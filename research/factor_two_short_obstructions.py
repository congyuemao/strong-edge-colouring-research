"""Independent endpoint checks of two sufficient-condition obstructions.

Only Python's standard library is used.  No downloaded inputs.
"""
from itertools import combinations
import json
from pathlib import Path


def edge(a, b):
    return (min(a, b), max(a, b))


def adjacency(n, edges):
    out = [set() for _ in range(n)]
    for a, b in edges:
        assert a != b
        out[a].add(b)
        out[b].add(a)
    return out


def conflict(n, edges, selected):
    ng = adjacency(n, edges)
    out = [set() for _ in selected]
    for i, (a, b) in enumerate(selected):
        for j in range(i):
            c, d = selected[j]
            if {a, b} & {c, d} or any(y in ng[x] for x in (a, b) for y in (c, d)):
                out[i].add(j)
                out[j].add(i)
    return out


def color(adj, k, omit=None):
    col = [-1] * len(adj)
    todo = set(range(len(adj))) - ({omit} if omit is not None else set())

    def dfs():
        if not todo:
            return col[:]
        v = max(todo, key=lambda x: (len({col[y] for y in adj[x] if col[y] >= 0}), len(adj[x]), -x))
        used = {col[y] for y in adj[v] if col[y] >= 0}
        todo.remove(v)
        for c in range(k):
            if c not in used:
                col[v] = c
                ans = dfs()
                if ans is not None:
                    return ans
        col[v] = -1
        todo.add(v)
        return None

    return dfs()


def no_short_cycles(adj):
    # A triangle creates adjacent vertices with a common neighbor.
    assert all(not (adj[v] & adj[u]) for v in range(len(adj)) for u in adj[v])
    # A four-cycle exists iff a pair has two distinct common neighbors.
    seen = set()
    for ns in adj:
        for pair in combinations(sorted(ns), 2):
            assert pair not in seen, ("four-cycle", pair)
            seen.add(pair)


def domination_obstruction():
    n = 20
    vertex = lambda i, j: 5 * (i % 4) + j % 5
    red = [edge(vertex(i, j), vertex(i, j + 1)) for i in range(4) for j in range(5)]
    blue = [edge(vertex(i, j), vertex(i + 1, 2 * j + (1 if i == 3 else 0)))
            for i in range(4) for j in range(5)]
    edges = set(red + blue)
    assert len(edges) == 40
    adj = adjacency(n, edges)
    assert {len(x) for x in adj} == {4}
    no_short_cycles(adj)
    h = conflict(n, edges, red)
    assert {len(x) for x in h} == {12}
    layers = [set(range(5 * i, 5 * i + 5)) for i in range(4)]
    assert all(all(b in h[a] for a, b in combinations(layer, 2)) for layer in layers)
    # Four independent vertices would select one from each layer.
    independents4 = []
    for a in layers[0]:
        for b in layers[1]:
            for c in layers[2]:
                for d in layers[3]:
                    q = [a, b, c, d]
                    if all(y not in h[x] for x, y in combinations(q, 2)):
                        independents4.append(q)
    assert not independents4
    witness3 = [2, 7, 12]
    assert all(y not in h[x] for x, y in combinations(witness3, 2))
    return {"G_vertices": n, "G_edges": sorted(edges), "F_edges": red,
            "H_degree": 12, "independence_number": 3,
            "independent_three_F_indices": witness3,
            "independent_four_count": len(independents4),
            "triple_domination_requires_at_least": 4}


def high_clique_obstruction():
    # Red-star centers B,E,G,H; red edge pq. The core's only cycle has length six.
    red = [(0, 6), (0, 7), (1, 8), (1, 9),
           (2, 10), (2, 11), (3, 12), (3, 13), (4, 5)]
    blue = [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5)]
    core = set(map(lambda x: edge(*x), red + blue))
    hc = conflict(14, core, red)
    expected = set(combinations(range(4), 2))
    expected |= set(combinations((0, 1, 4, 5), 2))
    expected |= set(combinations((2, 3, 6, 7), 2))
    expected |= {(4, 8), (5, 8), (6, 8), (7, 8)}
    actual = {(i, j) for i in range(9) for j in hc[i] if i < j}
    assert actual == expected
    assert [len(x) for x in hc] == [5, 5, 5, 5, 4, 4, 4, 4, 4]
    cliques4 = [list(q) for q in combinations(range(9), 4)
                if all(b in hc[a] for a, b in combinations(q, 2))]
    assert cliques4 == [[0, 1, 2, 3], [0, 1, 4, 5], [2, 3, 6, 7]]
    assert all(len(set(a) & set(b)) <= 2 for a, b in combinations(cliques4, 2))
    assert color(hc, 4) is None
    five_color = color(hc, 5)
    deletion_colorings = [color(hc, 4, v) for v in range(9)]
    assert all(c is not None for c in deletion_colorings)

    # Complete the colored bipartite core by a finite (Z_17)^2 cover.
    left = [0, 3, 4, 8, 9, 10, 11]
    right = [1, 2, 5, 6, 7, 12, 13]
    assert all((a in left) != (b in left) for a, b in core)
    added = []
    for label, old in [("red", red), ("blue", blue)]:
        ng = adjacency(14, old)
        ls = [v for v in left for _ in range(2 - len(ng[v]))]
        rs = [v for v in right for _ in range(2 - len(ng[v]))]
        assert len(ls) == len(rs)
        added.extend((label, a, b) for a, b in zip(ls, rs))
    assert len(added) == 14
    modulus = 17
    fiber = modulus * modulus
    vertex = lambda v, x, y: v * fiber + x * modulus + y
    lifted_edges = set()
    lifted_red = set()
    def add_lift(label, a, b, t):
        if a not in left:
            a, b = b, a
        for x in range(modulus):
            for y in range(modulus):
                e = edge(vertex(a, x, y), vertex(b, (x + t) % modulus, (y + t * t) % modulus))
                assert e not in lifted_edges
                lifted_edges.add(e)
                if label == "red":
                    lifted_red.add(e)
    for a, b in red:
        add_lift("red", a, b, 0)
    for a, b in blue:
        add_lift("blue", a, b, 0)
    for t, (label, a, b) in enumerate(added, 1):
        add_lift(label, a, b, t)
    n = 14 * fiber
    adj = adjacency(n, lifted_edges)
    fr = adjacency(n, lifted_red)
    assert {len(x) for x in adj} == {4}
    assert {len(x) for x in fr} == {2}
    no_short_cycles(adj)
    selected = [edge(vertex(a, 0, 0), vertex(b, 0, 0)) for a, b in red]
    lifted_hc = conflict(n, lifted_edges, selected)
    assert lifted_hc == hc
    return {"H_vertices": 9, "H_edges": sorted(actual), "H_degree": [len(x) for x in hc],
            "four_cliques": cliques4, "chromatic_number": 5,
            "five_coloring": five_color, "vertex_deletion_four_colorings": deletion_colorings,
            "core_G_vertices": 14, "core_red_edges": red, "core_blue_edges": blue,
            "completion_added_base_edges": added, "completion_group_modulus": modulus,
            "completion_G_vertices": n, "completion_G_edges": len(lifted_edges),
            "completion_F_edges": len(lifted_red), "completion_girth": 6,
            "completion_induced_selected_conflict_checked": True}


if __name__ == "__main__":
    result = {"triple_domination": domination_obstruction(),
              "degree_five_clique": high_clique_obstruction()}
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({"triple_domination": {"n": 20, "alpha": 3},
                      "high_clique": {"n": 9, "chi": 5, "completion_n": 4046},
                      "output": str(path)}, indent=2))
