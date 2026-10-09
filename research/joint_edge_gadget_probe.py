"""Controlled family only: replace low-low edges by a four-clique gadget.

This is not all critical graphs, and accepted pairs are only necessary local
conditions. The first round starts with O9 and the explicit 13-point core.
"""
from itertools import combinations
from pathlib import Path
import json
from joint_ore_probe import base
from joint_thirteen_probe import build


def replace(edges, edge):
    n = 1 + max(x for e in edges for x in e)
    u, v = edge
    result = edges - {edge}
    result |= set(combinations(range(n, n+4), 2))
    result |= {(u, n), (u, n+1), (v, n+2), (v, n+3)}
    return result


def inspect(edges):
    n = 1 + max(x for e in edges for x in e)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    clique = lambda vs: all(v in adj[u] for u,v in combinations(vs,2))
    k4 = [set(s) for s in combinations(range(n), 4) if clique(s)]
    if any(len(s&t) == 3 for s,t in combinations(k4,2)):
        return adj, []
    accepted = []
    for u,v in combinations(range(n),2):
        if v in adj[u]:
            continue
        old = {x: len(adj[x]-{u,v}) for x in range(n) if x not in (u,v)}
        if max(old.values()) > 4:
            continue
        sat = [[x for x in adj[t] if old[x] == 4] for t in (u,v)]
        if any(len(s) > 3 or not clique(s) for s in sat):
            continue
        common = adj[u] & adj[v]
        path = any(b in adj[a] and c in adj[b] and c not in adj[a]
                   for a,b,c in __import__('itertools').permutations(common,3))
        neighbourhood_delta = [max((len(adj[x]&adj[t]) for x in adj[t]), default=0) for t in (u,v)]
        accepted.append({'pair':[u,v], 'sat':sat, 'common':sorted(common),
                         'N_delta':neighbourhood_delta,
                         'common_path_repair':path and max(neighbourhood_delta)<=2})
    return adj, accepted


def main():
    rows = []
    for name, edges in [('O9',base()[0]), ('J13',build()[0])]:
        adj,_ = inspect(edges)
        for edge in sorted(edges):
            if any(len(adj[x]) != 4 for x in edge):
                continue
            out = replace(edges,edge)
            _, pairs = inspect(out)
            rows.append({'base':name, 'replaced':edge, 'vertices':len(adj)+4,
                         'edges':sorted(out), 'accepted_pairs':pairs})
    result = {'scope':'Only one low-low edge replacement in each named base; no exhaustive classification.',
              'rows':rows}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    for r in rows:
        if r['accepted_pairs']:
            print(json.dumps({k:v for k,v in r.items() if k!='edges'}))
    print('graphs',len(rows),'accepted',sum(bool(r['accepted_pairs']) for r in rows))


if __name__ == '__main__':
    main()
