"""Full girth-seven completion preserving C7[K2] minus one red edge.

Short-cover obstruction forms include all cyclically nonbacktracking closed
walks of lengths 3..6, not merely simple cycles.
"""
from pathlib import Path
from collections import Counter
import random
import json
from joint_thirteen_realization import graph, girth, conflict

n = 7
centres = list(range(n))
aa = list(range(n,2*n))
bb = list(range(2*n,3*n))
red_old = [tuple(sorted((i,j))) for i in centres for j in (aa[i],bb[i])]
blue_old = [tuple(sorted((i,(i+1)%n))) for i in centres]
red_new = [tuple(sorted((aa[i],bb[(i+1)%n]))) for i in centres]
blue_new = [tuple(sorted((side[i],side[(i+1)%n]))) for side in (aa,bb) for i in centres]
old = set(red_old+blue_old)
added = red_new+blue_new
edges = old | set(added)
assert len(edges)==42
adj = graph(21,edges)
assert all(len(ns)==4 for ns in adj)
assert all(len(ns)==2 for ns in graph(21,red_old+red_new))
index = {e:i for i,e in enumerate(added)}
forms = set()
counts = Counter()
for start in range(21):
    def walk(path, coefficient):
        cur=path[-1]
        for nxt in adj[cur]:
            if len(path)>1 and nxt==path[-2]:
                continue
            ee=tuple(sorted((cur,nxt)))
            cc=coefficient[:]
            if ee in index:
                cc[index[ee]] += 1 if cur<nxt else -1
            length=len(path)
            if nxt==start and 3<=length<=6 and path[1]!=cur:
                counts[length]+=1
                assert any(cc), (path,nxt)
                k=next(x for x in cc if x)
                if k<0:cc=[-x for x in cc]
                forms.add(tuple(cc))
            if length<6:
                walk(path+[nxt],cc)
    walk([start],[0]*len(added))
modulus=101
rng=random.Random(700713)
attempts=0
while True:
    attempts+=1
    voltages=[rng.randrange(1,modulus) for _ in added]
    if all(sum(a*b for a,b in zip(form,voltages))%modulus for form in forms):
        break
voltage=dict(zip(added,voltages))
lifted=[]
lifted_red=[]
for x,y in sorted(edges):
    for k in range(modulus):
        e=tuple(sorted((x*modulus+k,y*modulus+(k+voltage.get((x,y),0))%modulus)))
        lifted.append(e)
        if (x,y) in set(red_old+red_new):lifted_red.append(e)
ladj=graph(21*modulus,lifted)
assert all(len(ns)==4 for ns in ladj)
assert all(len(ns)==2 for ns in graph(21*modulus,lifted_red))
assert girth(ladj)==7
target=[]
for i in range(13):
    for j in range(i+1,13):
        # Delete red_old[0]; preserved red indices are 1..13.
        ci,cj=(i+1)//2,(j+1)//2
        if ci==cj or (ci-cj)%7 in (1,6):target.append((i,j))
chosen=[(x*modulus,y*modulus) for x,y in red_old[1:]]
assert conflict(chosen,ladj)==set(target)
out={
    'scope':'Full G/F realization, not an optimal A/B/C partition.',
    'base_vertices':21,'red_old':red_old,'blue_old':blue_old,
    'red_new':red_new,'blue_new':blue_new,'modulus':modulus,
    'added_edge_voltages':list(zip(added,voltages)),
    'short_nonbacktracking_closed_walk_counts':dict(sorted(counts.items())),
    'voltage_forms':len(forms),'voltage_attempts':attempts,
    'full_vertices':len(ladj),'full_edges':len(lifted),
    'full_red_edges':len(lifted_red),'girth':7,
    'induced_core_edges':target,'induced_J7_preserved':True,
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in
 ('red_old','blue_old','red_new','blue_new','added_edge_voltages','induced_core_edges')}))
