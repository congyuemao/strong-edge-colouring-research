"""Exact finite list-coloring experiments on a cycle with two spokes per vertex."""
from itertools import combinations
from pathlib import Path
import random,time,json

def core(n):
    edges=[tuple(sorted((i,(i+1)%n))) for i in range(n)]
    edges += [(i,n+2*i+j) for i in range(n) for j in range(2)]
    adj=[set() for _ in range(3*n)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    masks=[0]*len(edges)
    for i,j in combinations(range(len(edges)),2):
        e,f=edges[i],edges[j]
        if set(e)&set(f) or any(y in adj[x] for x in e for y in f):
            masks[i]|=1<<j;masks[j]|=1<<i
    assert all(masks[i].bit_count()==12 for i in range(n))
    assert all(masks[i].bit_count()==9 for i in range(n,3*n))
    return edges,masks

class Limit(Exception):pass

def list_color(masks,lists,node_limit=1000000):
    domains=list(lists);assignment=[-1]*len(masks);remaining=(1<<len(masks))-1
    visits=0
    # Colors with exactly the same list-incidence can be permuted globally.
    palette=max(lists).bit_length()
    incidence=[sum(1<<v for v,L in enumerate(lists) if L>>c&1) for c in range(palette)]
    earlier_equiv=[sum(1<<b for b in range(c) if incidence[b]==incidence[c]) for c in range(palette)]
    def search(remaining,used):
        nonlocal visits
        visits+=1
        if visits>node_limit:raise Limit
        if not remaining:return assignment.copy()
        v=min((v for v in range(len(masks)) if remaining>>v&1),
              key=lambda v:(domains[v].bit_count(),-(masks[v]&remaining).bit_count(),v))
        candidates=domains[v]
        if not candidates:return None
        choices=[]
        while candidates:
            b=candidates&-candidates;candidates^=b;c=b.bit_length()-1
            if not used&b and earlier_equiv[c]&~used:continue
            impact=sum(1 for w in range(len(masks)) if remaining>>w&1 and masks[v]>>w&1 and domains[w]&b)
            choices.append((impact,b))
        for _,b in sorted(choices):
            assignment[v]=b.bit_length()-1
            changed=[];neighbors=masks[v]&remaining&~(1<<v);bad=False
            while neighbors:
                bit=neighbors&-neighbors;neighbors^=bit;w=bit.bit_length()-1
                if domains[w]&b:
                    changed.append(w);domains[w]^=b
                    if not domains[w]:bad=True
            answer=None if bad else search(remaining&~(1<<v),used|b)
            for w in changed:domains[w]|=b
            if answer is not None:return answer
            assignment[v]=-1
        return None
    start=time.monotonic()
    try:
        colors=search(remaining,0);status='sat' if colors is not None else 'unsat'
    except Limit:colors=None;status='limit'
    if colors is not None:
        assert all(lists[v]>>c&1 for v,c in enumerate(colors))
        assert all(colors[i]!=colors[j] for i,j in combinations(range(len(masks)),2) if masks[i]>>j&1)
    return dict(status=status,visits=visits,seconds=round(time.monotonic()-start,6),coloring=colors)

def run(trials=1000,seed=720185):
    rng=random.Random(seed);summary=[];hard=[]
    for n in [5,6,7,8,9,10,11,12]:
        edges,masks=core(n)
        uniform=[255]*n+[31]*(2*n)
        result=list_color(masks,uniform)
        print('uniform',n,result['status'],result['visits'],flush=True)
        if result['status']=='unsat':hard.append(dict(n=n,lists=uniform,**result))
        counts={'sat':0,'unsat':0,'limit':0};worst=(0,None)
        for t in range(trials):
            group_lists=[sum(1<<c for c in rng.sample(range(8),5)) for _ in range(n)]
            lists=[255]*n+[group_lists[i] for i in range(n) for _ in range(2)]
            result=list_color(masks,lists,node_limit=200000)
            counts[result['status']]+=1
            if result['visits']>worst[0]:worst=(result['visits'],dict(n=n,lists=lists,**result))
            if result['status']=='unsat':
                hard.append(dict(n=n,lists=lists,**result))
                print('BAD_LISTS',n,lists,result['visits'],flush=True)
                break
        summary.append(dict(n=n,uniform=result if trials==0 else None,counts=counts,max_visits=worst[0]))
        if worst[1]:hard.append(worst[1])
        print('random',n,counts,'max_nodes',worst[0],flush=True)
    return dict(seed=seed,summary=summary,hard_cases=hard)

if __name__=='__main__':
    r=run()
    Path('research/high_girth_list_experiments.json').write_text(json.dumps(r,indent=2))
