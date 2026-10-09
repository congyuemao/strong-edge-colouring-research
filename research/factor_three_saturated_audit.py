"""Independent verification of the raw 268-vertex planted certificate.

Never imports the generator, completion routine, cost function, or search.
It also records an explicit descending two-vertex swap if one exists.
"""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json


def main():
    source=Path(__file__).with_name('factor_three_saturated_realization_240_exchange.json')
    d=json.loads(source.read_text(encoding='utf-8'))
    red=[tuple(e) for e in d['red']]; blue=[tuple(e) for e in d['blue']]
    n=len(d['names']); a=[set() for _ in range(n)]
    assert len(set(red+blue))==len(red+blue)
    for u,v in red+blue:
        assert u!=v
        a[u].add(v);a[v].add(u)
    assert all(len(nb)==4 for nb in a)
    assert all(not(a[u]&a[v]) for u,v in red+blue)
    assert all(len(a[u]&a[v])<=1 for u,v in combinations(range(n),2))
    fa=[set() for _ in range(n)]
    for u,v in red: fa[u].add(v);fa[v].add(u)
    assert all(len(nb)==2 for nb in fa)
    unseen=set(range(n));cycle_lengths=[]
    while unseen:
        todo=[unseen.pop()]
        for v in todo:
            for w in fa[v]&unseen: unseen.remove(w);todo.append(w)
        cycle_lengths.append(len(todo))
    h=[set() for _ in red]
    for i,j in combinations(range(len(red)),2):
        if set(red[i])&set(red[j]) or any(y in a[x] for x in red[i] for y in red[j]):
            h[i].add(j);h[j].add(i)
    assert all(len(nb)==12 for nb in h)
    caps=[4,3,3]
    def counts(cs):
        return [[sum(cs[w]==c for w in nb) for c in range(3)] for nb in h]
    def potential(cs):
        return sum(cs[v]==cs[w] for v,nb in enumerate(h) for w in nb)//2-sum(caps[c] for c in cs)
    def bad_A(cs):
        unseen={v for v,c in enumerate(cs) if c==0};bad=[]
        while unseen:
            component={unseen.pop()};todo=list(component)
            for v in todo:
                for w in h[v]&unseen:
                    if cs[w]==0: unseen.remove(w);component.add(w);todo.append(w)
            if len(component)==5 and all(component-{v}<=h[v] for v in component):
                bad.append(sorted(component))
        return bad
    def verify_local(cs):
        deg=counts(cs)
        delta=[[deg[v][c]-deg[v][cs[v]]+caps[cs[v]]-caps[c] for c in range(3)]
               for v in range(len(red))]
        assert all(x>=0 for row in delta for x in row)
        assert all(deg[v][cs[v]]<=caps[cs[v]] for v in range(len(red)))
        return deg,delta
    cs=d['best']['colors'];deg,delta=verify_local(cs)
    q=d['q'][0];ws=d['q'][1:];Q=set(d['R'][0])|{q}
    assert cs[q]==0 and all(cs[w]==1 for w in ws)
    assert all(deg[v]==[4,4,4] for v in Q)
    assert all(deg[w]==[5,3,4] and h[w]&Q=={q} for w in ws)
    assert all(v in h[w] for v,w in combinations(ws,2))
    assert all(not(set(red[v])&set(red[w])) for v,w in combinations(ws,2))
    basebad=bad_A(cs);assert basebad==[sorted(Q)]
    states=[]
    for i,w in enumerate(ws,1):
        nxt=cs[:];nxt[q],nxt[w]=nxt[w],nxt[q]
        changed,_=verify_local(nxt)
        assert potential(nxt)==potential(cs)
        expected=set(d['R'][i])|{w}
        assert all(changed[v]==[4,4,4] for v in expected)
        assert bad_A(nxt)==[sorted(expected)]
        states.append({'swap':[q,w],'potential':potential(nxt),
                       'unique_A_K5':sorted(expected),'all_single_moves_nonnegative':True})
    negative=[]
    for v,w in combinations(range(len(red)),2):
        if cs[v]==cs[w]:continue
        change=delta[v][cs[w]]+delta[w][cs[v]]-2*(w in h[v])
        if change<0:negative.append((change,v,w))
    negative.sort()
    descent=None
    if negative:
        change,v,w=negative[0]
        nxt=cs[:];nxt[v],nxt[w]=nxt[w],nxt[v]
        assert potential(nxt)-potential(cs)==change
        descent={'swap':[v,w],'G_edges':[red[v],red[w]],'old_parts':[cs[v],cs[w]],
                 'change':change,'after_potential':potential(nxt)}
    out={'vertices':n,'edges':len(red+blue),'F_cycle_lengths':sorted(cycle_lengths),
         'part_sizes':dict(Counter(cs)),'potential':potential(cs),'unique_A_K5':sorted(Q),
         'three_saturated_private_neighbors':ws,'base_single_move_check':'passed',
         'zero_swap_states':states,'negative_pair_swaps_count':len(negative),
         'explicit_global_optimality_refutation':descent,
         'scope':'Local necessary conditions and zero-swap states verified. Not a global optimum.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print(json.dumps(out))


if __name__=='__main__':main()
