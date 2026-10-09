"""Verify the 13-point C7 blow-up core and all deletion color certificates."""
from itertools import combinations
from pathlib import Path
import json
from joint_gadget_tree_family import representatives, geometry


def main():
    clusters=[[0]]+[[2*i-1,2*i] for i in range(1,7)]
    vertex_cluster={v:i for i,vs in enumerate(clusters) for v in vs}
    edges={(u,v) for u,v in combinations(range(13),2)
           if (vertex_cluster[u]-vertex_cluster[v])%7 in (0,1,6)}
    adj=[0]*13
    for u,v in edges:
        adj[u]|=1<<v
        adj[v]|=1<<u
    assert geometry(adj)
    maximum_independent=max(len(s) for r in range(14) for s in combinations(range(13),r)
                            if all(not(adj[u]>>v&1) for u,v in combinations(s,2)))
    assert maximum_independent==3
    certificates=[]
    for removed in range(13):
        j=vertex_cluster[removed]
        four_sets=[{(i+o)%7 for o in (0,2,4)} for i in (1,2,j+1,j+2)]
        colors=[-1]*13
        for cluster,vertices in enumerate(clusters):
            available=[c for c,s in enumerate(four_sets) if cluster in s]
            surviving=[v for v in vertices if v!=removed]
            assert len(available)==len(surviving)
            for v,c in zip(surviving,available):
                colors[v]=c
        assert all(colors[u]!=colors[v] for u,v in edges if removed not in (u,v))
        certificates.append({'deleted':removed,'colors':colors})
    pairs=representatives(adj)
    types=sorted({tuple(sorted(vertex_cluster[v] for v in p['pair'])) for p in pairs})
    assert types==[(2,4),(2,5),(3,5)]
    assert len(pairs)==12
    result={'scope':'Abstract critical core and necessary representative pairs; no optimal partition certified.',
            'clusters':clusters,'edges':sorted(edges),'alpha':3,'chromatic_number':5,
            'deletion_certificates':certificates,'representative_pairs':pairs,
            'representative_cluster_types':types}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({'vertices':13,'edges':len(edges),'alpha':3,'representative_pairs':len(pairs),
                      'representative_cluster_types':types,'deletion_certificates':len(certificates)}))


if __name__=='__main__':
    main()
