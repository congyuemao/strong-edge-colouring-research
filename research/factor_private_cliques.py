"""Check every permitted endpoint-kernel gluing in the private-clique tables.

The graph cores below are written independently as raw edge strings.
This checks all roles/orientations in the proof's finite table, not a coloring.
"""
from itertools import combinations
from pathlib import Path
import json


FIVE = {
    '41': ('ab bc cd de xy', 'ae bx dy', 'xy'),
    '311': ('ab bc cd xy uv', 'bx dy cu av yv', 'xy'),
    '221': ('ab bc de ef xy', 'be ax cy dx fy', 'xy'),
    '11111': ('aA bB cC dD xy', 'aB bC cD dA AC BD ax cx by dy', 'xy'),
}
FOUR = {
    '31': ('ab bc cd xy', 'bx dy', 'xy'),
    '211_AA': ('ab bc xy uv', 'bx bu yv', 'xy'),
    '211_AB_A': ('ab bc xy uv', 'bx au cv yu', 'xy'),
    '211_AB_B': ('ab bc xy uv', 'bx au cv yu', 'uv'),
    '1111': ('aA bB cC dD', 'aB bC cD dA AC BD', 'aA'),
}


def edge(u,v):
    return tuple(sorted((u,v)))


def read_core(core, side, identify=None):
    qwords, extra, marked = core
    vertices = set(''.join((qwords + ' ' + extra).split()))
    labels = {v: (side, v) for v in vertices}
    if identify is not None:
        labels[marked[0]], labels[marked[1]] = identify
    q = {edge(labels[a],labels[b]) for a,b in qwords.split()}
    g = q | {edge(labels[a],labels[b]) for a,b in extra.split()}
    return g,q,edge(labels[marked[0]],labels[marked[1]])


def check(left, right, flip):
    g,q,marked = read_core(left,0)
    pairing = tuple(reversed(marked)) if flip else marked
    other,r,marked2 = read_core(right,1,pairing)
    assert marked == marked2
    def degrees(edges):
        a = {v:set() for e in edges for v in e}
        for u,v in edges:
            a[u].add(v); a[v].add(u)
        return a
    a,b = degrees(g),degrees(other)
    allowed = all(len(a[v])+len(b[v])-1 <= 4 for v in marked)
    if not allowed:
        return None
    all_edges, f = g|other,q|r
    adj, fred = degrees(all_edges), degrees(f)
    assert max(map(len, adj.values())) <= 4
    assert max(map(len, fred.values())) <= 2
    assert all(not(adj[u]&adj[v]) for u,v in all_edges)
    assert all(len(adj[u]&adj[v]) <= 1 for u,v in combinations(adj,2))
    def conflict(e,f):
        return bool(set(e)&set(f)) or any(y in adj[x] for x in e for y in f)
    assert all(conflict(e,f) for e,f in combinations(q,2))
    assert all(conflict(e,f) for e,f in combinations(r,2))
    private = r-{marked}
    assert all({f for f in q if conflict(e,f)} == {marked} for e in private)
    return {'G': sorted(all_edges), 'F': sorted(f), 'Q': sorted(q),
            'q': marked, 'private_clique': sorted(private), 'checks':'all passed'}


def main():
    result, counts = {}, {}
    for size, table in [(4,FIVE),(3,FOUR)]:
        rows = []
        for old, left in FIVE.items():
            row = {}
            for new, right in table.items():
                orientations = []
                for flip in (False,True):
                    witness = check(left,right,flip)
                    if witness is not None:
                        orientations.append(flip)
                        rows.append({'old':old,'new':new,'flip':flip,'witness':witness})
                row[new] = len(orientations)
            counts[f'private_{size}_{old}'] = row
        result[f'private_{size}'] = rows
    result['counts'] = counts
    assert counts['private_4_41'] == {'41':2,'311':2,'221':2,'11111':2}
    assert counts['private_4_311'] == {'41':2,'311':1,'221':0,'11111':0}
    for old in ('221','11111'):
        assert counts[f'private_4_{old}'] == {'41':2,'311':0,'221':0,'11111':0}
        assert counts[f'private_3_{old}'] == {
            '31':2,'211_AA':2,'211_AB_A':2,'211_AB_B':0,'1111':0}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(counts))
    print('All permitted gluing witnesses passed raw endpoint checks.')


if __name__ == '__main__':
    main()
