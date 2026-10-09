"""Target the last all-hard hanging-C5 case at its forced nuclear C edge.

Enumerate the internal F choices, complete missing ports by fresh trees,
and test the forced seven B neighbors. Passing is only a local result.
"""
from itertools import combinations
from pathlib import Path
from collections import Counter
import json

CORES = {
    '221': ('ab bc de ef xy', 'be ax cy dx fy'),
    'matching': ('aA bB cC dD xy', 'aB bC cD dA AC BD ax cx by dy'),
}


def edge(u,v): return tuple(sorted((u,v)))


def prepare(k1,k2):
    labels={}; g=set(); qs=[]
    for side,kind in enumerate(('221',k1,k2)):
        qwords,extras=CORES[kind]
        for c in sorted(set(''.join((qwords+' '+extras).split()))):
            labels[side,c]=len(labels)
        q={edge(labels[side,u],labels[side,v]) for u,v in qwords.split()}
        qs.append(q)
        g |= q | {edge(labels[side,u],labels[side,v]) for u,v in extras.split()}
    q0=edge(labels[0,'a'],labels[0,'b'])
    q1=edge(labels[1,'x'],labels[1,'y'])
    q2=edge(labels[2,'x'],labels[2,'y'])
    left=edge(labels[0,'a'],labels[1,'x'])
    middle=edge(labels[1,'y'],labels[2,'x'])
    right=edge(labels[2,'y'],labels[0,'a'])
    g.update((left,middle,right))
    base=set().union(*qs)|{left,middle}
    return g,base,qs,(q0,q1,q2),left,middle,right,labels[2,'y']


def internal_choices(g,base,root):
    red=Counter(v for e in base|{root} for v in e)
    if max(red.values())>2: return
    candidates=sorted(e for e in g-base-{root} if all(red[v]<2 for v in e))
    def rec(i,chosen):
        if i==len(candidates):
            yield base|{root}|set(chosen)
            return
        yield from rec(i+1,chosen)
        e=candidates[i]
        if all(red[v]<2 for v in e):
            for v in e: red[v]+=1
            chosen.append(e)
            yield from rec(i+1,chosen)
            chosen.pop()
            for v in e: red[v]-=1
    yield from rec(0,[])


def complete(g,f):
    adj={v:set() for e in g for v in e}
    red={v:set() for v in adj}
    g=set(g);f=set(f)
    for u,v in g: adj[u].add(v);adj[v].add(u)
    for u,v in f: red[u].add(v);red[v].add(u)
    depth={v:0 for v in adj};queue=list(adj)
    for u in queue:
        if depth[u]>=3:continue
        for is_red,target in ((True,2),(False,4)):
            while len(red[u] if is_red else adj[u])<target:
                assert len(adj[u])<4
                v=len(adj);adj[v]={u};red[v]=set();adj[u].add(v)
                g.add(edge(u,v))
                if is_red:
                    red[u].add(v);red[v].add(u);f.add(edge(u,v))
                depth[v]=depth[u]+1;queue.append(v)
    return adj,f


def main():
    rows=[]
    for k1,k2 in (('221','221'),('221','matching'),('matching','221'),('matching','matching')):
        g,base,qs,central,left,middle,right,t2=prepare(k1,k2)
        roots=sorted(e for e in g-base-{right} if t2 in e)
        counts=Counter();first=None
        for root in roots:
            for f in internal_choices(g,base,root):
                assert right not in f
                adj,fred=complete(g,f)
                def conflict(e,h):
                    return bool(set(e)&set(h)) or any(v in adj[u] for u in e for v in h)
                near=sorted(e for e in fred if e!=root and conflict(root,e))
                assert len(near)==12
                aq=set(near)&qs[2]
                assert len(aq)==4 and left in near and middle in near
                forced_b=set(near)-aq-{left}
                assert len(forced_b)==7
                degrees={e:sum(conflict(e,h) for h in forced_b if h!=e) for e in forced_b}
                bad=max(degrees.values())>3
                counts['tested']+=1
                counts['forced_B_degree_failure' if bad else 'passes']+=1
                if not bad and first is None:
                    first={'G_core':sorted(g),'F_core':sorted(f),'Q':list(map(sorted,qs)),
                           'central':central,'left':left,'middle':middle,'right':right,
                           'nuclear_C_root':root,'forced_B':sorted(forced_b),
                           'B_degrees':sorted(degrees.values())}
        rows.append({'types':[k1,k2],'counts':dict(counts),'first_local_pass':first})
    out={'scope':'Explicit local necessary-condition test, not a global optimal partition.',
         'rows':rows}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print(json.dumps([{k:v for k,v in r.items() if k!='first_local_pass'} for r in rows]))


if __name__=='__main__':main()
