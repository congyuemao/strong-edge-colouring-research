"""Exhaust a stated edge-gadget family, not all 5-critical graphs.

Every replacement raises its two old endpoints from degree 4 to degree 5.
Consequently replacement edges within one base block form a matching. A new
block is K4 with ordered 2+2 attachment; recursion lists every decoration,
without repetitions due only to commuting operations in different subtrees.
No intermediate graph is pruned. Only final graphs are filtered.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import json
from joint_ore_probe import base as o9_base


def matchings(edges, count):
    return [es for es in combinations(sorted(edges), count)
            if len({x for edge in es for x in edge}) == 2*count]


K4_EDGES = tuple(combinations(range(4), 2))


@lru_cache(None)
def trees(budget):
    if budget == 0:
        return ((),)
    result = []
    for edge in K4_EDGES:
        result.extend(((edge, tree),) for tree in trees(budget-1))
    if budget >= 2:
        for e1, e2 in matchings(K4_EDGES, 2):
            for b in range(budget-1):
                for t1, t2 in product(trees(b), trees(budget-2-b)):
                    result.append(((e1,t1),(e2,t2)))
    return tuple(result)


def root_trees(low_edges, budget):
    if budget == 0:
        yield ()
        return
    for edge in sorted(low_edges):
        for tree in trees(budget-1):
            yield ((edge,tree),)
    if budget >= 2:
        for e1,e2 in matchings(low_edges,2):
            for b in range(budget-1):
                for t1,t2 in product(trees(b),trees(budget-2-b)):
                    yield ((e1,t1),(e2,t2))


def construct(root_edges, decoration):
    edges = set(root_edges)
    n = 1+max(x for edge in edges for x in edge)
    def add(block, desc):
        nonlocal n
        for (i,j), children in desc:
            u,v = block[i],block[j]
            edges.remove(tuple(sorted((u,v))))
            fresh = list(range(n,n+4))
            n += 4
            edges.update(combinations(fresh,2))
            edges.update(tuple(sorted((u,x))) for x in fresh[:2])
            edges.update(tuple(sorted((v,x))) for x in fresh[2:])
            add(fresh,children)
    add(list(range(n)),decoration)
    adj = [0]*n
    for u,v in edges:
        adj[u] |= 1<<v
        adj[v] |= 1<<u
    return adj


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def clique(adj, mask):
    return all((mask ^ (1<<v)) & ~adj[v] == 0 for v in bits(mask))


def geometry(adj):
    # Every two K4s sharing three points give a triangle with 2 common neighbours.
    for a in range(len(adj)):
        for b in bits(adj[a] & ~((1<<(a+1))-1)):
            common = adj[a] & adj[b]
            for c in bits(common & ~((1<<(b+1))-1)):
                if (common & adj[c]).bit_count() >= 2:
                    return False
    return True


def representatives(adj):
    high = sum(1<<v for v,ns in enumerate(adj) if ns.bit_count()==5)
    answer=[]
    for u,v in combinations(range(len(adj)),2):
        if adj[u]>>v & 1:
            continue
        chosen=(1<<u)|(1<<v)
        if high & ~(adj[u]|adj[v]|chosen):
            continue
        sat_u=high & adj[u] & ~adj[v] & ~chosen
        sat_v=high & adj[v] & ~adj[u] & ~chosen
        if max(sat_u.bit_count(),sat_v.bit_count())>3:
            continue
        if not clique(adj,sat_u) or not clique(adj,sat_v):
            continue
        common=adj[u]&adj[v]
        path=any(sum(bool(adj[a]>>b&1) for a,b in combinations(t,2))==2
                 for t in combinations(list(bits(common)),3))
        n_delta=[max(((adj[x]&adj[t]).bit_count() for x in bits(adj[t])), default=0)
                 for t in (u,v)]
        repaired=(adj[u].bit_count()==adj[v].bit_count()==5 and path and max(n_delta)<=2)
        answer.append({'pair':[u,v], 'saturated':[list(bits(sat_u)),list(bits(sat_v))],
                       'common':list(bits(common)), 'N_delta':n_delta,
                       'common_path_repair':repaired})
    return answer


def main():
    o9,oadj=o9_base()
    roots=[('K5',set(combinations(range(5),2)),5),('O9',o9,3)]
    summary=[]
    survivors=[]
    for name,root,limit in roots:
        deg=Counter(x for edge in root for x in edge)
        lows=[edge for edge in root if all(deg[x]==4 for x in edge)]
        for budget in range(limit+1):
            count=Counter()
            for decoration in root_trees(lows,budget):
                count['constructed']+=1
                adj=construct(root,decoration)
                assert max(ns.bit_count() for ns in adj)<=5
                if not geometry(adj):
                    continue
                count['clique_geometry_pass']+=1
                pairs=representatives(adj)
                if not pairs:
                    continue
                count['representative_graphs']+=1
                count['representative_pairs']+=len(pairs)
                unrepaired=[p for p in pairs if not p['common_path_repair']]
                count['unfiltered_graphs']+=bool(unrepaired)
                count['unfiltered_pairs']+=len(unrepaired)
                survivors.append({'root':name,'replacements':budget,'decoration':decoration,
                                  'pairs':pairs})
            row={'root':name,'replacements':budget,'vertices':len(deg)+4*budget,**count}
            summary.append(row)
            print(json.dumps(row),flush=True)
    result={'scope':'Exactly the rooted labelled gadget-tree family: K5 at most 5 replacements and O9 at most 3; not all critical graphs.',
            'attachment_subtree_counts':[len(trees(i)) for i in range(5)],
            'summary':summary,'survivors':survivors}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
