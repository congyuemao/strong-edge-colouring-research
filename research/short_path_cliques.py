"""Five strong-cliques in the explicitly constructed Petersen graph.

This only tests the suggested shape lemma, not the 20-color question.
"""
import json
from itertools import combinations
from pathlib import Path


def main():
    vertices = list(combinations(range(5), 2))
    edges = [(i, j) for i in range(10) for j in range(i)
             if not (set(vertices[i]) & set(vertices[j]))]
    adjacency = [set() for _ in vertices]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    def conflicts(e, f):
        return bool(set(e) & set(f)) or any(y in adjacency[x]
                                           for x in e for y in f)
    examples, counts = {}, {}
    for chosen in combinations(range(len(edges)), 5):
        if not all(conflicts(edges[e], edges[f])
                   for e, f in combinations(chosen, 2)):
            continue
        local = [set() for _ in vertices]
        for e in chosen:
            u, v = edges[e]
            local[u].add(v)
            local[v].add(u)
        if max(map(len, local)) > 2:
            continue
        unseen = {v for v, nb in enumerate(local) if nb}
        sizes, forest = [], True
        while unseen:
            component = {unseen.pop()}
            queue = list(component)
            for v in queue:
                for w in local[v] - component:
                    component.add(w)
                    unseen.remove(w)
                    queue.append(w)
            size = sum(len(local[v]) for v in component) // 2
            if size == len(component):
                forest = False
            sizes.append(size)
        if not forest:
            continue
        key = ','.join(map(str, sorted(sizes, reverse=True)))
        counts[key] = counts.get(key, 0) + 1
        examples.setdefault(key, {
            'edge_indices': list(chosen),
            'edges': [edges[e] for e in chosen],
            'edge_endpoint_labels': [[vertices[v] for v in edges[e]]
                                     for e in chosen]})
    result = {'vertex_labels': vertices, 'edges': edges,
              'forest_clique_shape_counts': counts, 'examples': examples}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
