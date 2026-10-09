"""Exact standard-library DSATUR experiments for spliced 20-edge examples.

Outcomes are computations, not a theorem for arbitrary graph sizes.
Every returned coloring is independently checked against the original graph.
"""
from itertools import combinations
import time
import json

def tight_edges(offset=0):
    return {tuple(sorted((offset+2*i+j, offset+2*((i+1)%5)+k)))
            for i in range(5) for j in range(2) for k in range(2)}

def conflict_graph(n, edges):
    edges = sorted(edges)
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v); adj[v].add(u)
    assert max(map(len, adj)) <= 4
    masks = [0] * len(edges)
    for i,j in combinations(range(len(edges)),2):
        e,f = edges[i],edges[j]
        if set(e)&set(f) or any(v in adj[u] for u in e for v in f):
            masks[i] |= 1<<j; masks[j] |= 1<<i
    return edges,masks

class Timeout(Exception): pass

def exact_color(masks, k, initial_clique=(), limit=20.0):
    n=len(masks)
    color=[-1]*n
    domains=[0]*n
    allcolors=(1<<k)-1
    start=time.monotonic()
    visits=0
    for c,v in enumerate(initial_clique):
        assert c<k
        assert all(masks[v]>>w&1 for w in initial_clique[:c])
        color[v]=c
        for w in range(n):
            if masks[v]>>w&1: domains[w] |= 1<<c
    uncolored=sum(1<<v for v in range(n) if color[v]<0)
    def dfs(uncolored, used):
        nonlocal visits
        visits+=1
        if visits%1024==0 and time.monotonic()-start>limit: raise Timeout
        if not uncolored: return list(color)
        chosen=-1; best=(-1,-1)
        left=uncolored
        while left:
            b=left&-left; v=b.bit_length()-1; left^=b
            rank=(domains[v].bit_count(),(masks[v]&uncolored).bit_count())
            if rank>best: chosen=v; best=rank
        v=chosen
        available=allcolors&~domains[v]&((1<<min(used+1,k))-1)
        if not available: return None
        candidates=[]
        while available:
            b=available&-available; available^=b
            impact=sum(1 for w in range(n) if uncolored>>w&1 and masks[v]>>w&1 and not domains[w]&b)
            candidates.append((impact,b))
        for _,b in sorted(candidates):
            c=b.bit_length()-1
            color[v]=c
            changed=[]
            left=masks[v]&uncolored&~(1<<v)
            failure=False
            while left:
                bit=left&-left; w=bit.bit_length()-1; left^=bit
                if not domains[w]&b:
                    changed.append(w); domains[w]|=b
                    if domains[w]==allcolors: failure=True
            answer=None if failure else dfs(uncolored&~(1<<v),max(used,c+1))
            for w in changed: domains[w]^=b
            if answer is not None: return answer
            color[v]=-1
        return None
    try:
        answer=dfs(uncolored,len(initial_clique))
        status='sat' if answer is not None else 'unsat'
    except Timeout:
        answer=None; status='timeout'
    if answer is not None:
        assert all(0<=c<k for c in answer)
        assert all(answer[i]!=answer[j] for i,j in combinations(range(n),2) if masks[i]>>j&1)
    return dict(k=k,status=status,visits=visits,seconds=round(time.monotonic()-start,3),coloring=answer)

def graph_splice(copies, crossed=False):
    edges=set()
    for i in range(copies):
        edges |= tight_edges(10*i)
        edges.remove((10*i,10*i+2))
    if copies==2 and not crossed:
        edges |= {(0,10),(2,12)}
    else:
        for i in range(copies):
            edges.add(tuple(sorted((10*i+2,10*((i+1)%copies)))))
    return 10*copies,edges

def canonical_deleted_coloring():
    edges=tight_edges();edges.remove((0,2))
    coloring={(0,8):0,(2,4):0,(0,9):1,(2,5):1,(0,3):2,(1,2):3}
    for c,e in enumerate(sorted(edges-set(coloring)),4): coloring[e]=c
    return coloring

def explicit_cycle_coloring(copies):
    """The constructive 17-color theorem for every cycle of >=2 gadgets."""
    assert copies>=2
    canonical=canonical_deleted_coloring()
    # Two independent 3-colorings: adjacent connector edges receive distinct
    # colors, and adjacent gadgets use disjoint four-color boundary blocks.
    gadget_colors=[i%2 for i in range(copies)]
    if copies%2: gadget_colors[-1]=2
    connector_colors=gadget_colors
    coloring={}
    for i in range(copies):
        palette={c:3+4*gadget_colors[i]+c for c in range(4)}
        # Canonical color 9 belongs only to edge (4,6), nonconflicting with
        # an incoming edge at port 0. Color 13 belongs only to (6,8),
        # nonconflicting with an outgoing edge at port 2.
        palette[9]=connector_colors[(i-1)%copies]
        palette[13]=connector_colors[i]
        remaining=[c for c in range(17) if c not in palette.values()]
        for canonical_c,new_c in zip([c for c in range(17) if c not in palette],remaining):
            palette[canonical_c]=new_c
        for (u,v),c in canonical.items(): coloring[(10*i+u,10*i+v)]=palette[c]
        coloring[tuple(sorted((10*i+2,10*((i+1)%copies))))]=connector_colors[i]
    n,edges=graph_splice(copies,crossed=True)
    es,masks=conflict_graph(n,edges)
    assert set(es)==set(coloring)
    assert all(coloring[es[i]]!=coloring[es[j]]
               for i,j in combinations(range(len(es)),2) if masks[i]>>j&1)
    return dict(name='explicit_cycle_'+str(copies),vertices=n,edges=es,
                coloring=[coloring[e] for e in es],colors=len(set(coloring.values())))

def run_case(name,n,edges,ks=(17,18,19,20)):
    es, masks=conflict_graph(n,edges)
    # Copy 0 after deletion contains an explicit 17-edge conflict clique.
    clique=[i for i,e in enumerate(es) if max(e)<10 and e not in {(0,8),(0,9)}]
    assert len(clique)==17
    results=[]
    for k in ks:
        result=exact_color(masks,k,clique,limit=15)
        results.append(result)
        if result['status']=='sat': break
    return dict(name=name,vertices=n,edges=es,clique_lower_bound=17,results=results)

def run():
    results=[]
    e=tight_edges();e.remove((0,2))
    es,masks=conflict_graph(10,e)
    nonconflicting=[(es[i],es[j]) for i,j in combinations(range(19),2) if not masks[i]>>j&1]
    expected={tuple(sorted((a,b))) for a in [(0,8),(0,9)] for b in [(2,4),(2,5)]}
    assert {tuple(sorted(p)) for p in nonconflicting}==expected
    results.append(run_case('one_copy_deleted_edge',10,e))
    for copies in [2,3,4,5,6]:
        n,edges=graph_splice(copies)
        results.append(run_case('cycle_of_'+str(copies)+'_copies',n,edges))
    return results

if __name__=='__main__':
    from pathlib import Path
    result=run()
    Path('research/counterexample_splice_results.json').write_text(json.dumps(result,indent=2))
    for case in result:
        print(case['name'],[(r['k'],r['status'],r['visits'],r['seconds']) for r in case['results']])
