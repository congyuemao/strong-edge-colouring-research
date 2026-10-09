"""Search the abstract graph class in factor_two_saturated.md 14.3.

This is a generator of explicitly checked members, not an exhaustive generator.
Non-3-colourability is decided by exhaustive DSATUR, with a saved graph for
independent checking and subsequent critical-core extraction.
"""
import json, random, time
from pathlib import Path


def three_color(a):
    n=len(a); col=[-1]*n; nodes=0
    # The first designated triangle fixes global colour symmetry.
    col[0]=0; col[1]=1; col[2]=2
    def rec(left):
        nonlocal nodes
        nodes+=1
        if not left:return col.copy()
        best=-1;opts=None;key=None
        for v in left:
            seen={col[w] for w in a[v] if col[w]>=0}
            if len(seen)==3:return None
            k=(len(seen),sum(w in left for w in a[v]))
            if key is None or k>key:
                best=v;key=k;opts=[c for c in range(3) if c not in seen]
        rest=left-{best}
        for c in opts:
            col[best]=c
            z=rec(rest)
            if z is not None:return z
        col[best]=-1
        return None
    return rec(set(range(n))-{0,1,2}),nodes


def validate(a,h):
    n=len(a);high=set(range(0,3*h,3))
    assert all(len(a[v])==4 for v in high)
    assert all(len(a[v])==3 for v in range(n) if v not in high)
    assert all(not(a[v]&high) for v in high)
    for q in high:
        s,t=q+1,q+2
        assert t in a[s] and a[s]&a[t]=={q}
        assert a[s]&high=={q} and a[t]&high=={q}
    # Exclude an unrelated cubic K4 component.
    for v in range(n):
        if len(a[v])==3 and all(y in a[x] for x in a[v] for y in a[v] if x!=y):
            return False
    seen={0};front=[0]
    while front:
        v=front.pop()
        for w in a[v]-seen:seen.add(w);front.append(w)
    return len(seen)==n


def generate(rng,h,p):
    n=3*h+p
    for attempt in range(300):
        a=[set() for _ in range(n)]
        def edge(u,v):a[u].add(v);a[v].add(u)
        for q in range(0,3*h,3):
            edge(q,q+1);edge(q,q+2);edge(q+1,q+2)
        ordinary=list(range(3*h,n));cap={v:3 for v in ordinary}
        ok=True
        for q in rng.sample(list(range(0,3*h,3)),h):
            choices=[v for v in ordinary if cap[v]]
            if len(choices)<2:ok=False;break
            u,v=rng.sample(choices,2)
            for x in (u,v):edge(q,x);cap[x]-=1
        if not ok:continue
        stubs=[v for v in range(n) for _ in range((4 if v%3==0 and v<3*h else 3)-len(a[v]))]
        rng.shuffle(stubs)
        while stubs:
            u=stubs.pop()
            choices=[i for i,v in enumerate(stubs) if v!=u and v not in a[u]]
            if not choices:ok=False;break
            i=rng.choice(choices);v=stubs.pop(i);edge(u,v)
            if u<3*h and u%3:
                q=u-u%3;s,t=q+1,q+2
                if a[s]&a[t]!={q}:ok=False;break
            if v<3*h and v%3:
                q=v-v%3;s,t=q+1,q+2
                if a[s]&a[t]!={q}:ok=False;break
        if ok and validate(a,h):return a
    return None


def main():
    rng=random.Random(14937);rows=[];start=time.time();tried=0
    hardest=(0,None)
    for h in range(2,13):
        for p in range(2,2*h+3,2):
            if 3*p<2*h:continue
            generated=0;mx=0
            for _ in range(80):
                a=generate(rng,h,p)
                if a is None:continue
                tried+=1;generated+=1
                coloring,nodes=three_color(a);mx=max(mx,nodes)
                if nodes>hardest[0]:hardest=(nodes,(h,p))
                if coloring is None:
                    result={'status':'non_3_colorable','high_count':h,'ordinary_count':p,
                            'adj':[sorted(z) for z in a],'nodes':nodes,
                            'tried':tried,'elapsed':time.time()-start,'rows':rows}
                    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
                    print(json.dumps({k:v for k,v in result.items() if k not in ('adj','rows')}),flush=True)
                    return
                assert all(coloring[u]!=coloring[v] for u in range(len(a)) for v in a[u])
            rows.append({'h':h,'p':p,'generated':generated,'max_nodes':mx})
        print('finished h',h,'tried',tried,'hardest',hardest,'seconds',round(time.time()-start,3),flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'all_samples_3_colorable','tried':tried,'hardest':hardest,'rows':rows},indent=2))


if __name__=='__main__':main()
