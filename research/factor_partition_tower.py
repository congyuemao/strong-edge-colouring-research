"""Exact (4,3,3)-potential on a real high-girth two-factor family.

Each layer is a red C5. Blue edges send j to 2j mod 5 in the next layer.
For >=5 layers, the original graph is 4-regular and has girth at least 5.
Red conflicts within each layer are K5; between neighboring layers they
are K5,5 minus the matching j -> 2j+3. Dynamic programming is exhaustive.
"""
import json
from itertools import product
from pathlib import Path
import numpy as np


STATES = np.array(list(product(range(3), repeat=5)), dtype=np.int16)
COUNTS = np.stack([(STATES == c).sum(axis=1) for c in range(3)], axis=1)
UNARY = ((COUNTS * (COUNTS - 1)).sum(axis=1) // 2
         - COUNTS @ np.array([4, 3, 3]))
PSI = np.array([(2*j + 3) % 5 for j in range(5)])
PAIR = COUNTS @ COUNTS.T - (STATES[:, None, :] == STATES[None, :, PSI]).sum(axis=2)
LOOKUP = {tuple(s): i for i, s in enumerate(STATES.tolist())}
INF = 10000


def solve(layers, start, first=None, last=None, reconstruct=False):
    dp = np.full(len(STATES), INF, dtype=np.int32)
    if first is None:
        dp[start] = UNARY[start]
        path_prefix, steps = [], layers-1
    else:
        dp[first] = UNARY[start] + PAIR[start, first] + UNARY[first]
        path_prefix, steps = [start], layers-2
    parents = []
    for step in range(steps):
        candidates = dp[:, None] + PAIR
        if reconstruct:
            parents.append(candidates.argmin(axis=0))
        dp = candidates.min(axis=0) + UNARY
    terminal = dp + PAIR[:, start]
    end = int(terminal.argmin()) if last is None else last
    value = int(terminal[end])
    if not reconstruct:
        return value
    path = [end]
    for parent in reversed(parents):
        end = int(parent[end])
        path.append(end)
    path.reverse()
    path = path_prefix + path
    assert len(path) == layers
    assert value == sum(int(UNARY[s]) for s in path) + sum(
        int(PAIR[path[i], path[(i+1) % layers]]) for i in range(layers))
    return value, path


def build_and_verify(layers, partition):
    def vertex(i, j):
        return (i % layers)*5 + (j % 5)
    red = [(vertex(i, j), vertex(i, j+1))
           for i in range(layers) for j in range(5)]
    blue = [(vertex(i, j), vertex(i+1, 2*j))
            for i in range(layers) for j in range(5)]
    adjacent = [set() for _ in range(5*layers)]
    for u, v in red + blue:
        assert u != v and v not in adjacent[u]
        adjacent[u].add(v)
        adjacent[v].add(u)
    assert all(len(a) == 4 for a in adjacent)
    assert all(not (adjacent[u] & adjacent[v]) for u, v in red+blue)
    assert all(len(adjacent[u] & adjacent[v]) <= 1
               for u in range(5*layers) for v in range(u))
    conflicts = [set() for _ in red]
    for i, e in enumerate(red):
        for j, f in enumerate(red[:i]):
            if set(e) & set(f) or any(y in adjacent[x] for x in e for y in f):
                conflicts[i].add(j)
                conflicts[j].add(i)
    assert all(len(nb) == 12 for nb in conflicts)
    colors = sum([STATES[s].tolist() for s in partition], [])
    degrees = [[sum(colors[j] == c for j in nb) for c in range(3)]
               for nb in conflicts]
    phi = sum(degrees[v][colors[v]] for v in range(len(red))) // 2
    phi -= sum([4, 3, 3][c] for c in colors)
    targets = [4, 3, 3]
    def counts(assignment):
        return [[sum(assignment[j] == c for j in nb) for c in range(3)]
                for nb in conflicts]
    def bad_components(assignment):
        out = []
        for color in range(3):
            unseen = {v for v, c in enumerate(assignment) if c == color}
            while unseen:
                component = {unseen.pop()}
                queue = list(component)
                for v in queue:
                    for w in conflicts[v] & unseen:
                        if assignment[w] == color:
                            unseen.remove(w)
                            component.add(w)
                            queue.append(w)
                if (len(component) == targets[color]+1 and all(
                        component-{v} <= conflicts[v] for v in component)):
                    out.append({'part': color, 'vertices': sorted(component)})
        return out
    original_bad = bad_components(colors)
    repair = None
    if all(colors[v] == 0 and degrees[v] == [4, 4, 4] for v in range(5)):
        for w in range(5, len(red)):
            old = colors[w]
            for new in range(3):
                if new == old:
                    continue
                delta = degrees[w][new]-degrees[w][old]+targets[old]-targets[new]
                if delta:
                    continue
                after = colors[:]
                after[w] = new
                dc = counts(after)
                if any(dc[v][c] > targets[c] for v, c in enumerate(after)):
                    continue
                for v in range(5):
                    for target in (1, 2):
                        delta2 = dc[v][target]-dc[v][0]+targets[0]-targets[target]
                        if delta2:
                            continue
                        final = after[:]
                        final[v] = target
                        df = counts(final)
                        if any(df[z][c] > targets[c] for z, c in enumerate(final)):
                            continue
                        final_bad = bad_components(final)
                        if len(final_bad) < len(original_bad):
                            repair = {'moves': [[w, old, new], [v, 0, target]],
                                      'final_partition': final,
                                      'bad_components_after': final_bad}
                            break
                    if repair:
                        break
                if repair:
                    break
            if repair:
                break
    return {'vertices': 5*layers, 'red_edges': red, 'blue_edges': blue,
            'partition': colors, 'part_neighbor_counts': degrees,
            'potential_verified': phi,
            'min_single_move_delta': min(
                degrees[v][j]-degrees[v][c]+targets[c]-targets[j]
                for v, c in enumerate(colors) for j in range(3) if j != c),
            'bad_components': original_bad,
            'two_zero_move_repair': repair,
            'maximum_internal_degrees': [max(
                (degrees[v][c] for v in range(len(red)) if colors[v] == c),
                default=0) for c in range(3)],
            'root_K5_strict': all(colors[v] == 0 and degrees[v] == [4, 4, 4]
                                  for v in range(5))}


def main():
    results = []
    for layers in range(5, 10):
        candidates = [solve(layers, s) for s in range(len(STATES))]
        optimum = min(candidates)
        start = candidates.index(optimum)
        _, best_path = solve(layers, start, reconstruct=True)
        strict_value, strict_args = INF, None
        for raw_first in product((1, 2), repeat=5):
            first = LOOKUP[raw_first]
            raw_last = tuple(3-raw_first[int(PSI[PSI[j]])] for j in range(5))
            last = LOOKUP[raw_last]
            value = solve(layers, 0, first, last)
            if value < strict_value:
                strict_value, strict_args = value, (first, last)
        _, strict_path = solve(layers, 0, *strict_args, reconstruct=True)
        global_certificate = build_and_verify(layers, best_path)
        strict_certificate = build_and_verify(layers, strict_path)
        assert global_certificate['potential_verified'] == optimum
        assert strict_certificate['potential_verified'] == strict_value
        assert strict_certificate['root_K5_strict']
        result = {'layers': layers, 'global_minimum': optimum,
                  'minimum_with_strict_bad_K5': strict_value,
                  'gap': strict_value-optimum,
                  'global_certificate': global_certificate,
                  'strict_certificate': strict_certificate}
        results.append(result)
        print(json.dumps({k: v for k, v in result.items()
                          if not k.endswith('certificate')}), flush=True)
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(results, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
