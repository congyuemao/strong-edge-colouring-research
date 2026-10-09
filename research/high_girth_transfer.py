"""Exact finite-state verifier for periodically repeated cycle lists."""
from itertools import combinations
from collections import deque
from pathlib import Path
import json

def automaton(pattern,cycle_lists=None):
    period=len(pattern)
    if cycle_lists is None:cycle_lists=[255]*period
    palette=max(pattern+cycle_lists).bit_length()
    pairs=[[sum(1<<c for c in p) for p in combinations([c for c in range(palette) if L>>c&1],2)] for L in pattern]
    layers=[];states=[];lookups=[]
    for i in range(period):
        layer=[];lookup={}
        for s,t in ((s,t) for s in pairs[i] for t in pairs[(i+1)%period] if not s&t):
            possible=[c for c in range(palette) if not (s|t)>>c&1]
            for a in possible:
                if not cycle_lists[(i-1)%period]>>a&1:continue
                for b in possible:
                    if a==b or not cycle_lists[i]>>b&1:continue
                    state=(s,t,a,b)
                    index=len(states);states.append((i,state));layer.append(index);lookup[state]=index
        layers.append(layer);lookups.append(lookup)
    adjacency=[[] for _ in states]
    for v,(i,(s,t,a,b)) in enumerate(states):
        for u in pairs[(i+2)%period]:
            if t&u or u>>b&1:continue
            for c in range(palette):
                if c in (a,b) or (s|t|u)>>c&1 or not cycle_lists[(i+1)%period]>>c&1:continue
                adjacency[v].append(lookups[(i+1)%period][(t,u,b,c)])
    return states,adjacency,layers

def directed_core(adjacency):
    """Delete vertices of out-degree zero until a fixed point."""
    reverse=[[] for _ in adjacency]
    for v,neighbors in enumerate(adjacency):
        for w in neighbors:reverse[w].append(v)
    degree=list(map(len,adjacency));queue=deque(v for v,d in enumerate(degree) if not d)
    deleted=[];rank=[None]*len(adjacency)
    while queue:
        v=queue.popleft();rank[v]=len(deleted);deleted.append(v)
        for w in reverse[v]:
            degree[w]-=1
            if degree[w]==0:queue.append(w)
    return dict(vertices=len(adjacency),arcs=sum(map(len,adjacency)),deleted=len(deleted),
                remaining=[v for v,r in enumerate(rank) if r is None],topological_deletion_order=deleted)

def exact_period_walk(states,adjacency,layers,length):
    for start in layers[0]:
        current={start}
        for _ in range(length):current={w for v in current for w in adjacency[v]}
        if start in current:return True
    return False

def closed_start_count(adjacency,layers,length=None):
    if length is None:length=len(layers)
    starts={v:i for i,v in enumerate(layers[0])}
    current={v:1<<i for v,i in starts.items()}
    for _ in range(length):
        following={}
        for v,origins in current.items():
            for w in adjacency[v]:following[w]=following.get(w,0)|origins
        current=following
    return sum(bool(current.get(v,0)>>i&1) for v,i in starts.items())

if __name__=='__main__':
    pattern=[115,115,143,143,124,124]
    states,adjacency,layers=automaton(pattern)
    result=directed_core(adjacency)
    print({k:v for k,v in result.items() if k not in ('remaining','topological_deletion_order')},flush=True)
    print('core_size',len(result['remaining']),flush=True)
    tests={}
    if result['remaining']:
        for n in [6,12,18,24,30]:
            tests[str(n)]=exact_period_walk(states,adjacency,layers,n)
            print(n,tests[str(n)],flush=True)
    Path('research/high_girth_periodic_automaton.json').write_text(json.dumps(dict(pattern=pattern,states=states,adjacency=adjacency,core=result,tests=tests),separators=(',',':')))
