"""A limited local obstruction test for F edges internal to a bad Q5 kernel.

This does not search global optimal partitions. Fresh tree continuations give
one minimal local model for each admissible internal F choice. We only test
the necessary induced-degree condition on the eight non-Q root neighbors.
"""
from itertools import combinations
from pathlib import Path
import json

CORES = {
    '41': ('ab bc cd de xy', 'ae bx dy'),
    '311': ('ab bc cd xy uv', 'bx dy cu av yv'),
    '221': ('ab bc de ef xy', 'be ax cy dx fy'),
    'matching': ('aA bB cC dD xy', 'aB bC cD dA AC BD ax cx by dy'),
}


def probe(name, text, extra, selected, root):
    chars = sorted(set(''.join((text+' '+extra).split())))
    ids = {v:i for i,v in enumerate(chars)}
    edge = lambda u,v: tuple(sorted((u,v)))
    q = {edge(ids[u],ids[v]) for u,v in text.split()}
    g = q | {edge(ids[u],ids[v]) for u,v in extra.split()}
    f = q | {edge(ids[u],ids[v]) for u,v in selected}
    root = edge(ids[root[0]],ids[root[1]])
    adj = {i:set() for i in ids.values()}
    red = {i:set() for i in ids.values()}
    for u,v in g:
        adj[u].add(v); adj[v].add(u)
    for u,v in f:
        red[u].add(v); red[v].add(u)
    if max(map(len,red.values())) > 2:
        return None
    depth = {i:0 for i in adj}
    queue = list(adj)
    for u in queue:
        if depth[u] >= 3:
            continue
        for is_red, target in ((True,2),(False,4)):
            while len(red[u] if is_red else adj[u]) < target:
                if len(adj[u]) == 4:
                    return None
                v = len(adj)
                adj[v]={u}; red[v]=set()
                adj[u].add(v)
                g.add(edge(u,v))
                if is_red:
                    red[u].add(v); red[v].add(u)
                    f.add(edge(u,v))
                depth[v]=depth[u]+1
                queue.append(v)
    def conflict(e,h):
        return bool(set(e)&set(h)) or any(v in adj[u] for u in e for v in h)
    near = sorted(h for h in f if h != root and conflict(root,h))
    assert len(near) == 12
    aq = set(near)&q
    outside = sorted(set(near)-q)
    assert len(aq) == 4 and len(outside) == 8
    h = {e:{z for z in outside if z!=e and conflict(e,z)} for e in outside}
    allowed = []
    for discard in [set()] + [{z} for z in outside]:
        keep = set(outside)-discard
        if all(len(h[z]&keep)<=3 for z in keep):
            allowed.append(sorted(discard))
    return {'type':name, 'selected':[''.join(e) for e in selected],
            'root':list(root), 'outside':outside,
            'outside_degrees':sorted(map(len,h.values())),
            'possible_single_same_part_neighbors':allowed,
            'local_degree_obstruction':not allowed}


def main():
    rows=[]
    for name,(qwords,extras) in CORES.items():
        es=[tuple(x) for x in extras.split()]
        for k in range(1,len(es)+1):
            for selected in combinations(es,k):
                for root in selected:
                    r=probe(name,qwords,extras,selected,root)
                    if r is not None:
                        rows.append(r)
    out={'scope':'Local tree-continuation test only; no global impossibility claims.',
         'count':len(rows), 'obstructions':sum(r['local_degree_obstruction'] for r in rows),
         'rows':rows}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print({k:v for k,v in out.items() if k!='rows'})


if __name__=='__main__':
    main()
