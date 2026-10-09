"""Independent direct checks of saved high-conflict strong-clique witnesses."""
from pathlib import Path
from itertools import combinations
import json


def check(n, edges, q, minimum):
    edges = [frozenset(e) for e in edges]
    q = [frozenset(e) for e in q]
    assert len(edges) == len(set(edges))
    assert all(len(e) == 2 for e in edges)
    neighbor = [set() for _ in range(n)]
    for e in edges:
        u,v = tuple(e)
        neighbor[u].add(v)
        neighbor[v].add(u)
    assert max(map(len,neighbor)) <= 4
    def hit(e,f):
        return bool(e & f) or any(neighbor[u] & f for u in e)
    assert all(e in edges for e in q)
    assert all(hit(e,f) for e,f in combinations(q,2))
    degrees = [sum(f != e and hit(e,f) for f in edges) for e in q]
    assert min(degrees) >= minimum
    return degrees


def pad(n, base):
    edges = list(map(tuple,base))
    for u in range(n):
        degree = sum(u in e for e in base)
        for _ in range(4-degree):
            w = n
            n += 4
            edges.extend([(u,w),(w,w+1),(w,w+2),(w,w+3)])
    return n,edges


if __name__ == '__main__':
    cert = json.loads(Path('research/high_conflict_nine_certificate.json').read_text())
    assert check(cert['vertex_count'],cert['edges'],cert['strong_clique'],23) == [23]*9
    profile = json.loads(Path('research/high_conflict_blowup_subgraphs.json').read_text())
    answer = {}
    for d,rec in profile['best'].items():
        n,edges = pad(10,rec['base_edges'])
        c = check(n,edges,rec['clique'],int(d))
        assert c == rec['degrees']
        answer[d] = dict(size=len(c),conflict_degrees=c)
    print(json.dumps(dict(nine_verified=True,threshold_witnesses=answer)))
