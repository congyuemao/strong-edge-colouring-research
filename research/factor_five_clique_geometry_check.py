"""Independent endpoint checks for the pure five-clique geometry proof.

Only standard library.  No previously generated graph or coloring is imported.
The finite search exhausts graphs on the endpoints of prescribed Q edges:
every conflict of two disjoint Q edges must have its witness in this set.
This audits the small core classifications, not arbitrary graph coloring.
"""
from itertools import combinations
from pathlib import Path
import json


def canon(u, v):
    return tuple(sorted((u, v)))


def adjacency(n, edges):
    a = [set() for _ in range(n)]
    for u, v in edges:
        a[u].add(v)
        a[v].add(u)
    return a


def admissible(a, u, v):
    if u == v or v in a[u] or len(a[u]) >= 4 or len(a[v]) >= 4:
        return False
    if a[u] & a[v]:
        return False
    return not any(a[x] & a[v] for x in a[u])


def conflict(a, e, f):
    return bool(set(e) & set(f)) or any(v in a[u] for u in e for v in f)


def make_paths(parts):
    q, offset = [], 0
    for length in parts:
        q += [(offset+i, offset+i+1) for i in range(length)]
        offset += length + 1
    return offset, tuple(q)


def core_models(n, q):
    """All endpoint graphs, not just minimal witness graphs."""
    initial = frozenset(q)
    visited, minimal = set(), set()

    def force(edges):
        if edges in visited:
            return
        visited.add(edges)
        a = adjacency(n, edges)
        options = []
        for e, f in combinations(q, 2):
            if conflict(a, e, f):
                continue
            available = {canon(u, v) for u in e for v in f
                         if admissible(a, u, v)}
            if not available:
                return
            options.append(available)
        if not options:
            minimal.add(edges)
            return
        for e in min(options, key=len):
            force(edges | {e})

    force(initial)
    all_models = set(minimal)
    stack = list(minimal)
    while stack:
        edges = stack.pop()
        a = adjacency(n, edges)
        for u, v in combinations(range(n), 2):
            if admissible(a, u, v):
                next_edges = edges | {(u, v)}
                if next_edges not in all_models:
                    all_models.add(next_edges)
                    stack.append(next_edges)
    return sorted(all_models, key=lambda x: (len(x), sorted(x)))


def check_named_witness(name, edge_words, q_words, extension_words):
    names = sorted(set(''.join(edge_words)))
    label = {v: i for i, v in enumerate(names)}
    convert = lambda es: [canon(label[e[0]], label[e[1]]) for e in es]
    edges, q, extension = map(convert, (edge_words, q_words, extension_words))
    assert len(set(edges)) == len(edges)
    a = adjacency(len(names), edges)
    assert max(map(len, a)) <= 4
    for u, v in edges:
        rest = adjacency(len(names), set(edges) - {(u, v)})
        assert admissible(rest, u, v)
    assert max(map(len, adjacency(len(names), q + extension))) <= 2
    assert all(conflict(a, e, f) for e, f in combinations(q, 2))
    assert all(conflict(a, e, f) for e in q for f in extension)
    assert all(not conflict(a, e, f) for e, f in combinations(extension, 2))
    return {'name': name, 'edges': edge_words, 'Q': q_words,
            'extensions': extension_words, 'checks': 'all passed'}


def main():
    result = {'five_edge_forests': {}, 'four_edge_cores': {}, 'witnesses': []}
    five_shapes = [(5,), (4,1), (3,2), (3,1,1), (2,2,1), (2,1,1,1), (1,)*5]
    four_shapes = [(4,), (3,1), (2,2), (2,1,1), (1,)*4]
    for shapes, field in [(five_shapes, 'five_edge_forests'),
                          (four_shapes, 'four_edge_cores')]:
        for shape in shapes:
            n, q = make_paths(shape)
            models = core_models(n, q)
            count_by_size = {}
            for e in models:
                count_by_size[len(e)] = count_by_size.get(len(e), 0) + 1
            record = {'vertices': n, 'Q': q, 'count': len(models),
                      'counts_by_edges': count_by_size}
            if field == 'four_edge_cores':
                record['all_edges'] = [sorted(e) for e in models]
            elif models:
                record['example_edges'] = sorted(models[0])
            result[field][','.join(map(str, shape))] = record
            print(field, shape, len(models), count_by_size, flush=True)
    assert {s for s, r in result['five_edge_forests'].items() if r['count']} == {
        '4,1', '3,1,1', '2,2,1', '1,1,1,1,1'}
    result['witnesses'].append(check_named_witness(
        'four-edge path with three extensions',
        ['ab','bc','cd','de','ea','bx','xy','yd','bu','uv','vd'],
        ['ab','bc','cd','de'], ['ea','xy','uv']))
    result['witnesses'].append(check_named_witness(
        'two-edge path and two singletons with three extensions',
        ['ab','bc','xy','uv','bx','au','cv','yu','cz','yz','xw','vw'],
        ['ab','bc','xy','uv'], ['au','cz','xw']))
    # q_i=s_i t_i with s=(a,b,c,d), t=(A,B,C,D).
    result['witnesses'].append(check_named_witness(
        'four-edge matching with three extensions',
        ['aA','bB','cC','dD','aB','bC','cD','dA','AC','BD',
         'ax','cx','by','dy','xy'],
        ['aA','bB','cC','dD'], ['AC','BD','xy']))
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print('All assertions passed.')


if __name__ == '__main__':
    main()
