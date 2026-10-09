"""Extend the exact hanger exchange to the optional internal F edge dx.

Its forced B color and internal B degree 0 or 1 are the two remaining
possibilities. This auxiliary test reuses the already independently checked
potential solver; it is not a separate proof of its correctness.
"""
from pathlib import Path
from itertools import combinations
import json
from factor_hanger_energy import build,optimize,CORES


def main():
    rows=[]
    for t1 in CORES:
        for t2 in CORES:
            for choice in range(2):
                original,h,old,outside,meta=build(t1,t2,choice)
                # First nucleus labels are a,b,c,d,e,f,x,y -> integers 0..7.
                extra=(3,6)
                assert extra in map(tuple,meta['G_core']) and extra not in original
                totals=[[outside[i][c]+sum(old[j]==c for j in h[i]) for c in range(3)] for i in range(len(original))]
                f=original+[extra];colors=old+[1]
                adj={v:set() for e in meta['G_core'] for v in e}
                for u,v in meta['G_core']:adj[u].add(v);adj[v].add(u)
                hh=[set() for e in f]
                for i,j in combinations(range(len(f)),2):
                    e,z=f[i],f[j]
                    if set(e)&set(z) or any(b in adj[a] for a in e for b in z):hh[i].add(j);hh[j].add(i)
                for db in (0,1):
                    ds=totals+[[4,db,8-db]]
                    out=[[ds[i][c]-sum(colors[j]==c for j in hh[i]) for c in range(3)] for i in range(len(f))]
                    assert min(x for row in out for x in row)>=0
                    result=optimize(hh,colors,out,f)
                    rows.append({'types':[t1,t2],'choice':choice,'extra_B_degree':db,**result})
                    print(t1,t2,choice,db,result['original_objective'],result['minimum_objective'],result['optimal_leaf_tests'],flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')


if __name__=='__main__':main()
