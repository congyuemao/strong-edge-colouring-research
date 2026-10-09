"""Independent verifier: consume the endpoint JSON, not its producing code."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json


def main():
    path = Path(__file__).with_name('joint_thirteen_realization.json')
    data = json.loads(path.read_text(encoding='utf-8'))
    m = data['modulus']
    n = len(data['names']) * m
    red_base = {tuple(e) for e in data['partial_red'] + data['red_added']}
    blue_base = {tuple(e) for e in data['partial_blue'] + data['blue_added']}
    assert not red_base & blue_base
    volt = {tuple(e): value for e, value in data['added_edge_voltages']}
    adjacency = [set() for _ in range(n)]
    fred = set()
    for a, b in red_base | blue_base:
        shift = volt.get((a, b), 0)
        for i in range(m):
            x, y = a*m+i, b*m+(i+shift) % m
            assert x != y and y not in adjacency[x]
            adjacency[x].add(y)
            adjacency[y].add(x)
            if (a, b) in red_base:
                fred.add(tuple(sorted((x, y))))
    assert all(len(ns) == 4 for ns in adjacency)
    fd = Counter(x for edge in fred for x in edge)
    assert len(fd) == n and all(d == 2 for d in fd.values())

    # Search directly for any simple cycle of length 3, 4, or 5.
    paths = 0
    for start in range(n):
        def visit(route):
            nonlocal paths
            paths += 1
            last = route[-1]
            for other in adjacency[last]:
                if other == start:
                    assert len(route) < 3 or len(route) > 5, route
                elif other > start and other not in route and len(route) < 5:
                    visit(route + [other])
        visit([start])
    # Six old edges at fibre zero witness girth exactly six.
    witness = [0*m, 1*m, 5*m, 7*m, 6*m, 4*m]
    assert all(witness[(i+1) % 6] in adjacency[witness[i]] for i in range(6))

    selected = [(a*m, b*m) for a, b in data['partial_red']]
    assert all(tuple(sorted(e)) in fred for e in selected)
    collisions = set()
    for i, j in combinations(range(13), 2):
        e, f = selected[i], selected[j]
        ends_near_e = set(e) | adjacency[e[0]] | adjacency[e[1]]
        if set(f) & ends_near_e:
            collisions.add((i, j))
    reference = json.loads(Path(__file__).with_name('joint_thirteen_probe.json').read_text(encoding='utf-8'))
    assert collisions == {tuple(e) for e in reference['edges']}
    result = {'independent_verification': True, 'full_vertices': n,
              'full_edges': sum(map(len, adjacency))//2, 'F_edges': len(fred),
              'girth': 6, 'short_path_states': paths, 'induced_13_exact': True,
              'scope': 'No optimal-partition certificate asserted.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
