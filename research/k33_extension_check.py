"""Exercise the exact Hall-failure branch of the K3,3 extension proof.

All graph conflicts are recomputed from endpoints.  The finite test family is
supplementary to k33_reducibility.md, not a universal computation.
"""
from itertools import combinations
from pathlib import Path
from random import Random
import json

PALETTE = set(range(20))


def conflicts(edges):
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    assert max(map(len, adj.values())) <= 4
    out = [set() for _ in edges]
    for i, e in enumerate(edges):
        for j in range(i):
            f = edges[j]
            if set(e) & set(f) or any(y in adj[x] for x in e for y in f):
                out[i].add(j)
                out[j].add(i)
    return out


def check_colors(colors, conflict):
    for i, color in colors.items():
        assert color in PALETTE
        assert all(colors.get(j) != color for j in conflict[i])


def lists(indices, colors, conflict):
    return {i: PALETTE - {colors[j] for j in conflict[i] if j in colors}
            for i in indices}


def representatives(tables):
    owner = {}

    def augment(i, seen):
        for color in sorted(tables[i]):
            if color in seen:
                continue
            seen.add(color)
            if color not in owner or augment(owner[color], seen):
                owner[color] = i
                return True
        return False

    for i in tables:
        if not augment(i, set()):
            return None
    return {i: color for color, i in owner.items()}


def instance(seed):
    rng = Random(seed)
    edges = [(a, b) for a in range(3) for b in range(3, 6)]
    spokes = []
    outside = {}
    cursor = 6
    for p in range(6):
        x = cursor
        cursor += 1
        spokes.append(len(edges))
        edges.append((p, x))
        star = {0, 1, 2} if p < 3 else {3, 4, 5}
        # Nine distinct second-level colors give each spoke exactly eight
        # available colors, including its initially assigned color 6+p.
        second = rng.sample(sorted(PALETTE - star - {6+p}), 9)
        for offset, color in enumerate(sorted(star)):
            z = cursor
            cursor += 1
            outside[len(edges)] = color
            edges.append((x, z))
            for color2 in second[3*offset:3*offset+3]:
                outside[len(edges)] = color2
                edges.append((z, cursor))
                cursor += 1
    initial = dict(outside)
    initial.update({i: 6+p for p, i in enumerate(spokes)})
    return edges, spokes, outside, initial


def run(seed):
    edges, spokes, outside, initial = instance(seed)
    conflict = conflicts(edges)
    check_colors(initial, conflict)
    internal = list(range(9))
    bad = lists(internal, initial, conflict)
    assert len({tuple(sorted(v)) for v in bad.values()}) == 1
    assert all(len(v) == 8 for v in bad.values())
    assert representatives(bad) is None
    original = lists(spokes, outside, conflict)
    assert all(len(v) == 8 for v in original.values())
    pair = next((i, j) for i, j in combinations(spokes[:3], 2)
                if j not in conflict[i] and original[i] & original[j])
    i, j = pair
    common = min(original[i] & original[j])
    colors = dict(outside)
    colors.update({i: common, j: common})
    for f in spokes:
        if f not in colors:
            colors[f] = min(lists([f], colors, conflict)[f])
    assert len({colors[f] for f in spokes}) <= 5
    good = lists(internal, colors, conflict)
    assert all(len(v) >= 9 for v in good.values())
    extension = representatives(good)
    assert extension is not None
    colors.update(extension)
    assert len(colors) == len(edges)
    assert all(colors[f] == color for f, color in outside.items())
    check_colors(colors, conflict)
    return {"seed": seed, "edges": edges,
            "initial_colors": [initial.get(i) for i in range(len(edges))],
            "final_colors": [colors[i] for i in range(len(edges))],
            "same_color_spokes": pair}


def main():
    records = [run(20261009+i) for i in range(100)]
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(records, ensure_ascii=False), encoding='utf-8')
    print(json.dumps({"cases": len(records), "vertices_each": 84,
                      "edges_each": 87, "initial_internal_lists": 8,
                      "outside_preserved": True, "all_final_colors_valid": True}))


if __name__ == '__main__':
    main()
