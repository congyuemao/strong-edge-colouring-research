"""Check stored matchings directly from the user's endpoint conditions."""
import json
from itertools import combinations
from pathlib import Path

root = Path(__file__).resolve().parent
graphs = {g['sample']: g for g in json.loads(
    (root/'colouring_certificates.json').read_text())}
certs = json.loads((root/'packing_certificates.json').read_text())
for cert in certs:
    graph = graphs[cert['sample']]
    edges = [tuple(e) for e in graph['edges']]
    adjacency = set(edges) | {(v, u) for u, v in edges}
    selected = cert['selected']
    matching = cert['matching']
    assert len(set(selected)) == len(selected)
    assert len(set(matching)) == len(matching)
    assert set(matching) <= set(selected) <= set(range(len(edges)))
    for first, second in combinations(matching, 2):
        a, b = edges[first], edges[second]
        assert not set(a) & set(b)
        assert not any((x, y) in adjacency for x in a for y in b)
    assert 20*len(matching) >= len(selected)
print('Independently verified', len(certs), 'induced matching size certificates.')
