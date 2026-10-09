"""Independent checker for degree3_kempe_stable.json.

Unlike the construction program, this builds conflicts by checking every
pair of edges directly from the definition. It also computes a fresh whole
graph coloring by smallest-last greedy coloring.
"""
import heapq
from itertools import combinations, product
import json
from pathlib import Path


def load_and_conflicts(path):
    data = json.loads(path.read_text())
    edges = data["edges"]
    colors = data["colors"]
    roots = data["root_edges"]
    assert len(colors) == len(edges)
    assert len(set(tuple(sorted(e)) for e in edges)) == len(edges)
    n = 1 + max(v for e in edges for v in e)
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert max(map(len, adjacency)) <= 4
    assert len(adjacency[0]) == 3
    assert set(roots) == {i for i, e in enumerate(edges) if 0 in e}
    assert {i for i, c in enumerate(colors) if c is None} == set(roots)
    assert all(c is None or 1 <= c <= 20 for c in colors)
    conflict = [set() for _ in edges]
    for i, (u, v) in enumerate(edges):
        for j in range(i):
            x, y = edges[j]
            if (u == x or u == y or v == x or v == y
                    or x in adjacency[u] or y in adjacency[u]
                    or x in adjacency[v] or y in adjacency[v]):
                conflict[i].add(j)
                conflict[j].add(i)
                assert colors[i] is None or colors[j] is None or colors[i] != colors[j]
    return data, adjacency, conflict


def pair_components(colors, conflict, pair):
    mapping = {}
    parts = []
    for start, c in enumerate(colors):
        if c not in pair or start in mapping:
            continue
        index = len(parts)
        component = {start}
        mapping[start] = index
        todo = [start]
        while todo:
            e = todo.pop()
            for f in conflict[e]:
                if colors[f] in pair and f not in mapping:
                    mapping[f] = index
                    component.add(f)
                    todo.append(f)
        parts.append(component)
    return parts, mapping


def extension(colors, conflict, roots):
    palette = set(range(1, 21))
    lists = [palette - {colors[f] for f in conflict[e] if colors[f] is not None}
             for e in roots]
    for triple in product(*lists):
        if len(set(triple)) == 3:
            return triple
    return None


def verify_one_swap(data, conflict):
    colors, roots = data["colors"], data["root_edges"]
    palette = set(range(1, 21))
    boundary = [conflict[e] - set(roots) for e in roots]
    assert all(len(ns) == 18 for ns in boundary)
    assert all(palette - {colors[e] for e in ns} == {19, 20} for ns in boundary)
    checked, irrelevant = 0, 0
    for pair in combinations(range(1, 21), 2):
        parts, mapping = pair_components(colors, conflict, pair)
        for part in parts:
            if not any(part & ns for ns in boundary):
                irrelevant += 1
                continue
            checked += 1
            changed = colors.copy()
            for e in part:
                changed[e] = sum(pair) - changed[e]
            assert extension(changed, conflict, roots) is None
    print("independent pairwise proper-color check: passed")
    print("root degree / uncolored edges / 18-edge lists: passed")
    print("relevant Kempe components exhaustively checked:", checked)
    print("irrelevant components (cannot affect root lists):", irrelevant)
    return checked


def whole_graph_coloring(conflict):
    degrees = [len(ns) for ns in conflict]
    removed = [False] * len(conflict)
    heap = [(d, e) for e, d in enumerate(degrees)]
    heapq.heapify(heap)
    order = []
    degeneracy = 0
    while heap:
        d, e = heapq.heappop(heap)
        if removed[e] or degrees[e] != d:
            continue
        removed[e] = True
        order.append(e)
        degeneracy = max(degeneracy, d)
        for f in conflict[e]:
            if not removed[f]:
                degrees[f] -= 1
                heapq.heappush(heap, (degrees[f], f))
    coloring = [None] * len(conflict)
    for e in reversed(order):
        forbidden = {coloring[f] for f in conflict[e]}
        coloring[e] = next(c for c in range(1, degeneracy + 2) if c not in forbidden)
    assert all(coloring[e] != coloring[f] for e, ns in enumerate(conflict) for f in ns)
    print("conflict graph degeneracy:", degeneracy)
    print("fresh complete strong coloring uses:", max(coloring))
    assert max(coloring) <= 20
    return coloring


if __name__ == "__main__":
    source = Path(__file__).with_name("degree3_kempe_stable.json")
    data, adjacency, conflict = load_and_conflicts(source)
    verify_one_swap(data, conflict)
    complete = whole_graph_coloring(conflict)
    destination = source.with_name("degree3_complete_coloring.json")
    destination.write_text(json.dumps({"source": source.name, "colors": complete},
                                      separators=(",", ":")))
    print("complete coloring saved:", destination.name)
