"""Second implementation: enumerate replacement operation sequences.

This deliberately does not use the block-tree generator or its graph filter.
Different operation orders may give isomorphic graphs and are all retained.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json


def root_graph(kind):
    if kind=='K5':
        edges=set(combinations(range(5),2)); n=5
    else:
        edges=set()
        for block in [(0,1,2,3),(0,1,4,5),(2,3,6,7)]:
            edges.update(combinations(block,2))
        edges.update((i,8) for i in (4,5,6,7)); n=9
    rows=[0]*n
    for u,v in edges:
        rows[u]|=1<<v; rows[v]|=1<<u
    return tuple(rows)


def graph_pairs(rows):
    n=len(rows)
    deg=[r.bit_count() for r in rows]
    high={v for v in range(n) if deg[v]==5}
    adjacent=lambda u,v: bool(rows[u] & (1<<v))
    candidate=[]
    for p,q in combinations(range(n),2):
        if adjacent(p,q):
            continue
        if any(h not in (p,q) and not adjacent(h,p) and not adjacent(h,q) for h in high):
            continue
        old={v:deg[v]-int(adjacent(v,p))-int(adjacent(v,q)) for v in range(n) if v not in (p,q)}
        if max(old.values())>4:
            continue
        saturation=[[v for v in old if old[v]==4 and adjacent(v,t)] for t in (p,q)]
        if any(len(s)>3 or any(not adjacent(u,v) for u,v in combinations(s,2)) for s in saturation):
            continue
        candidate.append((p,q))
    if not candidate:
        return []
    # Direct K4 enumeration, independent of the triangle/common-neighbour test.
    complete4=[]
    for a in range(n):
        later=[v for v in range(a+1,n) if adjacent(a,v)]
        for rest in combinations(later,3):
            if all(adjacent(u,v) for u,v in combinations(rest,2)):
                complete4.append({a,*rest})
    if any(len(s&t)==3 for s,t in combinations(complete4,2)):
        return []
    result=[]
    for p,q in candidate:
        common=[v for v in range(n) if adjacent(p,v) and adjacent(q,v)]
        p3=any(sum(adjacent(u,v) for u,v in combinations(s,2))==2 for s in combinations(common,3))
        sparse=True
        for t in (p,q):
            ns=[v for v in range(n) if adjacent(t,v)]
            if len(ns)!=5 or any(sum(adjacent(v,w) for w in ns if w!=v)>2 for v in ns):
                sparse=False
        result.append((p,q,p3 and sparse))
    return result


def extensions(rows):
    n=len(rows)
    lows=[v for v in range(n) if rows[v].bit_count()==4]
    for u,v in combinations(lows,2):
        if not rows[u]>>v&1:
            continue
        new=list(rows)+[0]*4
        new[u]^=1<<v; new[v]^=1<<u
        for a,b in combinations(range(n,n+4),2):
            new[a]|=1<<b; new[b]|=1<<a
        for a,b in [(u,n),(u,n+1),(v,n+2),(v,n+3)]:
            new[a]|=1<<b; new[b]|=1<<a
        yield tuple(new)


def main():
    summaries=[]; unhandled=[]
    for kind,limit in [('K5',5),('O9',3)]:
        counts=[Counter() for _ in range(limit+1)]
        def visit(rows,depth):
            counts[depth]['operation_sequences']+=1
            pairs=graph_pairs(rows)
            counts[depth]['admissible_sequences']+=bool(pairs)
            counts[depth]['admissible_pairs']+=len(pairs)
            for p,q,repaired in pairs:
                if repaired:
                    counts[depth]['common_path_pairs']+=1
                elif kind=='O9' and depth<=1:
                    counts[depth]['previous_rotation_pairs']+=1
                else:
                    unhandled.append({'kind':kind,'depth':depth,'rows':rows,'pair':[p,q]})
            if depth<limit:
                for child in extensions(rows):
                    visit(child,depth+1)
        visit(root_graph(kind),0)
        for depth,count in enumerate(counts):
            row={'root':kind,'replacements':depth,**count}
            summaries.append(row); print(json.dumps(row),flush=True)
    assert not unhandled, unhandled[:1]
    out={'scope':'Every operation sequence in the same stated budgets, with repetitions; independently implemented representative and clique filters.',
         'summary':summaries,'unhandled_pairs':unhandled}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
