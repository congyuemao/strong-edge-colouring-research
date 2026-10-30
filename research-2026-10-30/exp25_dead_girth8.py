"""exp25: girth-8 counterexample to Lemma 5(b) at girth 8 -- a dead edge with only 4 D-edges.

LARGE_GIRTH Lemma 5(b) (MANUSCRIPT_zh Lemma 3.9(b)) claims: if h = uv is dead and neither u nor v
is a D-endpoint, then at least 6 D-edges take part.  The proof needs girth >= 9: a D-edge killing
the M_4-edges at two outer neighbours on opposite sides of uv closes a cycle of length 8.  This
script builds such a configuration (constructed by the 2026-10-31 review agent) and checks:
max degree 4, girth exactly 8, M_4 a matching, D an induced matching disjoint from M_4, u and v
not D-endpoints, all 6 outer neighbours of h covered by M_4, h and all 6 covering edges in N_D,
and only 4 D-edges involved.  At girth 8 the provable bound is 4, so this example is tight.

Run: python exp25_dead_girth8.py   (needs networkx)
"""
import networkx as nx

G = nx.Graph()
G.add_edge('u', 'v')
for i in (1, 2, 3):
    G.add_edge('u', f'o{i}'); G.add_edge(f'o{i}', f's{i}')
    G.add_edge('v', f'w{i}'); G.add_edge(f'w{i}', f't{i}')
M4 = [('u', 'v')] + [(f'o{i}', f's{i}') for i in (1, 2, 3)] + [(f'w{i}', f't{i}') for i in (1, 2, 3)]
D = [('o1', 'y0'), ('x1', 'y1'), ('x2', 'y2'), ('x3', 'y3')]
for a, b in D:
    G.add_edge(a, b)
G.add_edge('x1', 's2'); G.add_edge('y1', 't1')   # r1 kills o2s2 and w1t1: 8-cycle u o2 s2 x1 y1 t1 w1 v
G.add_edge('x2', 's3'); G.add_edge('y2', 't2')   # r2 kills o3s3 and w2t2
G.add_edge('x3', 't3')                           # r3 kills w3t3


def conflict(e1, e2):
    if set(e1) & set(e2):
        return True
    return any(G.has_edge(x, y) for x in e1 for y in e2)


assert max(d for _, d in G.degree()) == 4
assert nx.girth(G) == 8
vs = [x for e in M4 for x in e]
assert len(vs) == len(set(vs)), 'M4 not a matching'
assert all(not conflict(D[i], D[j]) for i in range(4) for j in range(i + 1, 4)), 'D not induced'
assert not (set(map(frozenset, D)) & set(map(frozenset, M4)))
assert not ({'u', 'v'} & {x for e in D for x in e}), 'u or v is a D-endpoint'
ND = [f for f in M4 if any(conflict(f, r) for r in D)]
h = ('u', 'v')
outer = (set(G['u']) | set(G['v'])) - {'u', 'v'}
cover = {x: f for f in M4 for x in f}
assert len(outer) == 6 and all(x in cover for x in outer)
covering = {cover[x] for x in outer}
assert h in ND and all(f in ND for f in covering), 'h is not dead'
involved = [r for r in D if any(conflict(f, r) for f in covering | {h})]
print({'max degree': 4, 'girth': nx.girth(G), 'h dead': True, 'D-edges involved': len(involved)})
