"""Explicit high-conflict strong clique and finite blowup-subgraph search.

No external packages or external graph data.  The subgraph search concerns
only strong cliques made from surviving base edges; its bounds are not
global graph-theoretic upper bounds.
"""
from itertools import combinations
from pathlib import Path
import json
from research.gadget_blocks import BASE, AUTOS, maximum_clique


def edges_normalized(edges):
    return sorted({tuple(sorted(e)) for e in edges})


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def conflict(e, f, adj):
    return bool(set(e) & set(f)) or any(y in adj[x] for x in e for y in f)


def pad_neighborhoods(n, edges):
    """Make every base vertex and each new base-neighbor 4-valent."""
    edges = edges_normalized(edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    assert max(deg, default=0) <= 4
    cursor = n
    for v in range(n):
        for _ in range(4-deg[v]):
            w = cursor
            cursor += 1
            edges.append((v, w))
            for _ in range(3):
                edges.append((w, cursor))
                cursor += 1
    return cursor, edges_normalized(edges)


def explicit_nine():
    # v,a,b,c,d,x,y,y',z,u,t,s, respectively.
    names = ['v', 'a', 'b', 'c', 'd', 'x', 'y', 'y_prime', 'z', 'u', 't', 's']
    q = [(0,1),(0,2),(0,3),(0,4),(1,5),(2,5),(1,6),(1,7),(2,8)]
    connectors = [(6,8),(7,8),(3,9),(4,9),(2,10),(10,11),(8,11)]
    base = edges_normalized(q + connectors)
    n, edges = pad_neighborhoods(12, base)
    adj = adjacency(n, edges)
    degrees = [sum(e != f and conflict(e,f,adj) for f in edges) for e in q]
    assert all(conflict(e,f,adj) for e,f in combinations(q,2))
    assert degrees == [23]*9, degrees
    assert max(map(len,adj)) == 4
    record = dict(vertex_count=n,edge_count=len(edges),base_names=names,
                  base_edges=base,strong_clique=q,conflict_degrees=degrees,edges=edges)
    Path('research/high_conflict_nine_certificate.json').write_text(json.dumps(record,indent=2))
    return {k:record[k] for k in ['vertex_count','edge_count','strong_clique','conflict_degrees']}


def blowup_subgraphs():
    seen = bytearray(1 << 20)
    records = {d:dict(size=0) for d in range(20,25)}
    orbit_count = 0
    coverage = 0
    for mask in range(1<<20):
        if seen[mask]:
            continue
        orbit = {sum(1<<p[e] for e in range(20) if mask>>e&1) for p in AUTOS}
        for m in orbit:
            seen[m] = 1
        coverage += len(orbit)
        orbit_count += 1
        es = [BASE[e] for e in range(20) if mask>>e&1]
        if len(es) <= min(r['size'] for r in records.values()):
            continue
        adj = adjacency(10,es)
        # Every base subgraph is triangle-free.  After neighborhood padding,
        # c(e)=24 minus the number of edges induced by the six other neighbors.
        # New tree neighbors contribute no edges to this induced set.
        c = []
        for u,v in es:
            outer = (adj[u]-{v}) | (adj[v]-{u})
            repeats = sum(a in outer and b in outer for a,b in es)
            c.append(24-repeats)
        for d,rec in records.items():
            candidates = [i for i,degree in enumerate(c) if degree>=d]
            if len(candidates) <= rec['size']:
                continue
            masks = [sum(1<<j for j,f in enumerate(candidates)
                         if i != j and conflict(es[e],es[f],adj))
                     for i,e in enumerate(candidates)]
            clique = [candidates[i] for i in maximum_clique(masks)]
            if len(clique)>rec['size']:
                records[d] = dict(size=len(clique),base_mask=mask,base_edges=es,
                                  clique=[es[i] for i in clique],
                                  degrees=[c[i] for i in clique])
    assert coverage == 1<<20
    result = dict(orbit_count=orbit_count,labeled_subgraphs=coverage,best=records)
    Path('research/high_conflict_blowup_subgraphs.json').write_text(json.dumps(result,indent=2))
    return result


if __name__ == '__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--subgraphs',action='store_true')
    args=parser.parse_args()
    print(json.dumps(explicit_nine()))
    if args.subgraphs:
        result=blowup_subgraphs()
        print(json.dumps(result))
