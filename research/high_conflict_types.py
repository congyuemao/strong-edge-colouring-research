"""Exact targeted search for a >=16 strong clique containing a 4-edge star.

All geometry is generated from neighborhood types, not graph catalogues.
The search may return a counterexample.  A negative result covers only
cliques with a vertex incident with four selected edges.
"""
from itertools import combinations, permutations
from pathlib import Path
from collections import Counter
import json
from research.counterexample_clique_bound import type_multisets

STARS = tuple((0,a) for a in range(1,5))


def high(adj, q, threshold=20):
    for u,v in q:
        aa = adj[u] & ~(1<<v)
        bb = adj[v] & ~(1<<u)
        common = (aa&bb).bit_count()
        if 4*common > 24-threshold:
            return False
        union = aa|bb
        internal = 0
        rest = union
        while rest:
            bit = rest & -rest
            rest ^= bit
            internal += (adj[bit.bit_length()-1]&rest).bit_count()
        if 4*common+internal > 24-threshold:
            return False
    return True


def put(adj,u,v):
    if adj[u]>>v&1:
        return True
    if adj[u].bit_count()==4 or adj[v].bit_count()==4:
        return False
    adj[u] |= 1<<v
    adj[v] |= 1<<u
    return True


def clash(adj,e,f):
    u,v=e
    x,y=f
    return u in f or v in f or bool((adj[u]|adj[v]) & ((1<<x)|(1<<y)))


def canonical_types(caps,has_internal):
    perms = [p for p in permutations(range(4))
             if not has_internal or {p[0],p[1]}=={0,1}]
    representatives=set()
    for ts in type_multisets(caps):
        s=sum(t.bit_count() for t in ts)
        k=sum(t.bit_count() in (2,3) for t in ts)
        if s+k+has_internal < 12:
            continue
        canon=min(tuple(sorted(sum(1<<p[i] for i in range(4) if t>>i&1)
                              for t in ts)) for p in perms)
        representatives.add(canon)
    return sorted(representatives)


def bb_choices(possible,base,h,start=0,picked=()):
    if h==0:
        yield picked,base
        return
    if len(possible)-start<h:
        return
    for i in range(start,len(possible)-h+1):
        x,y=possible[i]
        adj=base.copy()
        if put(adj,x,y):
            yield from bb_choices(possible,adj,h-1,i+1,picked+((x,y),))


def complete(adj,q,bb,counters):
    """Each unsatisfied disjoint pair of selected BB edges needs one connector."""
    clauses=[]
    for e,f in combinations(bb,2):
        if not clash(adj,e,f):
            options=[]
            for x in e:
                for y in f:
                    trial=adj.copy()
                    if put(trial,x,y) and high(trial,q):
                        options.append(tuple(sorted((x,y))))
            if not options:
                return None
            clauses.append(options)
    if not clauses:
        assert all(clash(adj,e,f) for e,f in combinations(q,2))
        return adj
    for x,y in min(clauses,key=len):
        trial=adj.copy()
        assert put(trial,x,y)
        counters['completion_nodes']+=1
        answer=complete(trial,q,bb,counters)
        if answer is not None:
            return answer
    return None


def run():
    counters=Counter()
    forced_survivors=[]
    patterns={a:canonical_types((3-a,3-a,3,3),a) for a in (0,1)}
    print('type patterns', {a:len(x) for a,x in patterns.items()},flush=True)
    for a,types_list in patterns.items():
        for ts in types_list:
            counters['type_patterns']+=1
            adj=[0]*(5+len(ts))
            for u,v in STARS:
                put(adj,u,v)
            if a:
                put(adj,1,2)
            ab=[]
            for j,t in enumerate(ts,5):
                for i in range(4):
                    if t>>i&1:
                        ab.append((i+1,j))
                        assert put(adj,i+1,j)
            if not high(adj,STARS):
                continue
            counters['root_valid_types']+=1
            possible=[(i+5,j+5) for i,j in combinations(range(len(ts)),2)
                      if ts[i]|ts[j]==15]
            k=sum(t.bit_count() in (2,3) for t in ts)
            for h in range(max(0,12-len(ab)-a),k+1):
                for bb,base in bb_choices(possible,adj,h):
                    rootq=STARS+bb
                    if not high(base,rootq):
                        continue
                    counters['bb_selections']+=1
                    for q_internal in range(a+1):
                        fixed=rootq+(((1,2),) if q_internal else ())
                        need=12-h-q_internal
                        candidates=[e for e in ab if high(base,fixed+(e,))
                                    and all(clash(base,e,f) for f in fixed)]
                        if len(candidates)<need:
                            continue
                        for selected in combinations(candidates,need):
                            counters['ab_selections']+=1
                            q=fixed+selected
                            trial=base.copy()
                            good=True
                            for e,f in combinations(selected,2):
                                if not clash(trial,e,f):
                                    x,y=e[1],f[1]
                                    if not put(trial,x,y):
                                        good=False
                                        break
                            if not good or not high(trial,q):
                                continue
                            counters['forced_valid']+=1
                            forced_survivors.append(dict(a=a,types=ts,bb=bb,ab=selected,
                                q_internal=q_internal,
                                edges=[(u,v) for u in range(len(trial))
                                       for v in range(u+1,len(trial)) if trial[u]>>v&1]))
                            answer=complete(trial,q,bb,counters)
                            if answer is not None:
                                edges=[(u,v) for u in range(len(answer))
                                       for v in range(u+1,len(answer)) if answer[u]>>v&1]
                                result=dict(found=True,types=ts,a=a,edges=edges,
                                            strong_clique=q,counters=dict(counters))
                                Path('research/high_conflict_types_result.json').write_text(json.dumps(result,indent=2))
                                return result
    result=dict(found=False,counters=dict(counters),pattern_counts={a:len(x) for a,x in patterns.items()},
                forced_survivors=forced_survivors)
    Path('research/high_conflict_types_result.json').write_text(json.dumps(result,indent=2))
    return result


if __name__=='__main__':
    print(json.dumps(run()))
