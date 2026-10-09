"""Exact fixed-boundary potential on the 18 known edges of the last hanger.

Boundary counts are the strict three-state consequences proved in the notes.
This is a local exchange test, not a global minimum partition certificate.
"""
from pathlib import Path
from itertools import combinations
import json

CORES={
 '221':('ab bc de ef xy','be ax cy dx fy'),
 'matching':('aA bB cC dD xy','aB bC cD dA AC BD ax cx by dy'),
}


def build(t1,t2,choice):
    labels={};g=set();qs=[]
    edge=lambda u,v:tuple(sorted((u,v)))
    for i,t in enumerate(('221',t1,t2)):
        qwords,extras=CORES[t]
        for c in sorted(set(''.join((qwords+' '+extras).split()))):
            labels[i,c]=len(labels)
        q={edge(labels[i,u],labels[i,v]) for u,v in qwords.split()}
        qs.append(q);g|=q|{edge(labels[i,u],labels[i,v]) for u,v in extras.split()}
    central=[edge(labels[0,'a'],labels[0,'b']),edge(labels[1,'x'],labels[1,'y']),edge(labels[2,'x'],labels[2,'y'])]
    left=edge(labels[0,'a'],labels[1,'x']);middle=edge(labels[1,'y'],labels[2,'x']);right=edge(labels[2,'y'],labels[0,'a'])
    g.update((left,middle,right))
    tip=labels[2,'y']
    nuclear=sorted(e for e in g if tip in e and e not in qs[2] and e!=right)[choice]
    f=sorted(set().union(*qs)|{left,middle,nuclear});idx={e:i for i,e in enumerate(f)}
    adj={v:set() for e in g for v in e}
    for u,v in g:adj[u].add(v);adj[v].add(u)
    def conflict(e,h):return bool(set(e)&set(h)) or any(v in adj[u] for u in e for v in h)
    h=[set() for e in f]
    for i,j in combinations(range(len(f)),2):
        if conflict(f[i],f[j]):h[i].add(j);h[j].add(i)
    colors=[None]*len(f);degrees=[None]*len(f)
    for k,q in enumerate(qs):
        for e in q:
            i=idx[e]
            if e==central[k]:
                colors[i]=0 if k==0 else 1
                degrees[i]=[4,4,4] if k==0 else [5,3,4]
            else:
                colors[i]=0
                degrees[i]=[4,4,4] if k==0 else [3,5,4]
    for e,c,ds in ((left,2,[5,5,2]),(middle,1,[4,2,6]),(nuclear,2,[4,7,1])):
        colors[idx[e]]=c;degrees[idx[e]]=ds
    outside=[]
    for i in range(len(f)):
        inside=[sum(colors[j]==c for j in h[i]) for c in range(3)]
        row=[degrees[i][c]-inside[c] for c in range(3)]
        assert min(row)>=0,(t1,t2,choice,f[i],row)
        outside.append(row)
    return f,h,colors,outside,{'Q':list(map(sorted,qs)),'central':central,'L':left,'M':middle,'f2':nuclear,'G_core':sorted(g)}


def optimize(h,old,outside,f):
    n=len(h);r=(4,3,3)
    unary=[[outside[i][c]-r[c] for c in range(3)] for i in range(n)]
    def energy(cs):
        return sum(unary[i][cs[i]] for i in range(n))+sum(cs[i]==cs[j] for i in range(n) for j in h[i] if i<j)
    assert all(row[0]==0 for row in outside)
    def tuple_score(cs,value):
        unseen={i for i,c in enumerate(cs) if c==0};bad=[]
        while unseen:
            v=next(iter(unseen));seen={v};queue=[v];unseen.remove(v)
            for u in queue:
                for z in (h[u]&unseen):
                    unseen.remove(z);seen.add(z);queue.append(z)
            if len(seen)==5 and all(len(h[u]&seen)==4 for u in seen):bad.append(seen)
        def shape(q):
            adj={v:set() for i in q for v in f[i]}
            for i in q:
                u,v=f[i];adj[u].add(v);adj[v].add(u)
            todo=set(adj);lengths=[]
            while todo:
                v=next(iter(todo));comp={v};todo.remove(v);queue=[v]
                for u in queue:
                    for z in adj[u]&todo:
                        todo.remove(z);comp.add(z);queue.append(z)
                lengths.append(sum(len(adj[u]) for u in comp)//2)
            return tuple(sorted(lengths,reverse=True))
        shapes=[shape(q) for q in bad]
        soft=sum(s in ((4,1),(3,1,1)) for s in shapes)
        count221=shapes.count((2,2,1))
        return (value,len(bad),-sum(c==0 for c in cs),-soft,-count221)
    original=energy(old);original_tuple=tuple_score(old,original)
    best_tuple=original_tuple;best=original;witness=list(old);nodes=0;leaves=0
    assigned=[-1]*n
    costs=[row[:] for row in unary]
    def search(left,score):
        nonlocal best,best_tuple,witness,nodes,leaves
        nodes+=1
        lower=score+sum(min(costs[i]) for i in left)
        if lower>best:return
        if not left:
            leaves+=1
            ts=tuple_score(assigned,score)
            if ts<best_tuple:
                best=score;best_tuple=ts;witness=assigned[:]
            return
        i=max(left,key=lambda i:(sorted(costs[i])[1]-min(costs[i]),len(h[i]&left),-i))
        others=left-{i}
        for c in sorted(range(3),key=lambda c:costs[i][c]):
            assigned[i]=c
            for j in h[i]&others:costs[j][c]+=1
            search(others,score+costs[i][c])
            for j in h[i]&others:costs[j][c]-=1
        assigned[i]=-1
    search(set(range(n)),0)
    assert energy(witness)==best
    return {'original_energy':original,'minimum_energy':best,'delta':best-original,
            'original_objective':original_tuple,'minimum_objective':best_tuple,
            'nodes':nodes,'optimal_leaf_tests':leaves,'coloring':witness}


def main():
    rows=[]
    for t1 in CORES:
        for t2 in CORES:
            for choice in range(2):
                f,h,old,outside,meta=build(t1,t2,choice)
                result=optimize(h,old,outside,f)
                row={'types':[t1,t2],'nuclear_choice':choice,'F_core':f,'old_colors':old,'outside_counts':outside,'structure':meta,**result}
                rows.append(row)
                print(t1,t2,choice,'objective',result['original_objective'],result['minimum_objective'],'nodes',result['nodes'],'leaves',result['optimal_leaf_tests'],flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')


if __name__=='__main__':main()
