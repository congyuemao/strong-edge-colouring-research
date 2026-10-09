"""Independent check of the full C7 core realization, from JSON only."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json


def main():
    data=json.loads(Path(__file__).with_name('joint_c7_cover.json').read_text(encoding='utf-8'))
    modulus=data['modulus']; n=data['base_vertices']*modulus
    fred_base={tuple(e) for e in data['red_old']+data['red_new']}
    blue_base={tuple(e) for e in data['blue_old']+data['blue_new']}
    assert not fred_base & blue_base
    voltage={tuple(e):value for e,value in data['added_edge_voltages']}
    adjacent=[set() for _ in range(n)]; fred=set()
    for x,y in fred_base|blue_base:
        for k in range(modulus):
            a=x*modulus+k; b=y*modulus+(k+voltage.get((x,y),0))%modulus
            assert a!=b and b not in adjacent[a]
            adjacent[a].add(b); adjacent[b].add(a)
            if (x,y) in fred_base:
                fred.add(tuple(sorted((a,b))))
    assert all(len(ns)==4 for ns in adjacent)
    degrees=Counter(x for edge in fred for x in edge)
    assert len(degrees)==n and all(d==2 for d in degrees.values())
    visited=0
    for start in range(n):
        def walk(path):
            nonlocal visited
            visited+=1
            for nxt in adjacent[path[-1]]:
                if nxt==start:
                    assert len(path)<3 or len(path)>6, path
                elif nxt>start and nxt not in path and len(path)<6:
                    walk(path+[nxt])
        walk([start])
    old_circle=[i*modulus for i in range(7)]
    assert all(old_circle[(i+1)%7] in adjacent[old_circle[i]] for i in range(7))
    chosen=[(a*modulus,b*modulus) for a,b in data['red_old'][1:]]
    assert all(tuple(sorted(e)) in fred for e in chosen)
    conflict=[]
    for i,j in combinations(range(13),2):
        a,b=chosen[i]
        if set(chosen[j]) & ({a,b}|adjacent[a]|adjacent[b]):
            conflict.append([i,j])
    abstract=json.loads(Path(__file__).with_name('joint_c7_blowup.json').read_text(encoding='utf-8'))
    assert conflict==abstract['edges']
    result={'independent_verification':True,'vertices':n,
            'edges':sum(map(len,adjacent))//2,'F_edges':len(fred),'girth':7,
            'short_path_states':visited,'induced_13_exact':True,
            'scope':'No optimal-partition certificate asserted.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result))


if __name__=='__main__':
    main()
