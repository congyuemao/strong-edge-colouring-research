"""Targeted completion of the four-matching / four-(4,1)-satellite core.

This searches for a complete G,F and a one-vertex-local minimum of the
(4,3,3) potential with the prescribed three saturated private neighbors.
Success is a method obstacle, NOT proof of a global minimum or a counterexample.
"""
import json
import math
import random
import sys
from itertools import combinations
from pathlib import Path


def edge(u,v):
    return tuple(sorted((u,v)))


def build(seed=93017, extra=80):
    rng = random.Random(seed)
    names, red, blue = [], set(), set()
    def vertex(name):
        names.append(name)
        return len(names)-1
    s = [vertex('s'+str(i)) for i in range(4)]
    t = [vertex('t'+str(i)) for i in range(4)]
    satellite = [[vertex(f'{i}{c}') for c in 'abcde'] for i in range(4)]
    qs, rs = [], []
    for i in range(4):
        q = edge(s[i],t[i]); red.add(q); qs.append(q)
        blue.add(edge(s[i],t[(i+1)%4]))
        a,b,c,d,e = satellite[i]
        path = [edge(a,b),edge(b,c),edge(c,d),edge(d,e)]
        red.update(path); rs.append(path)
        blue.update([edge(a,e),edge(s[i],b),edge(t[i],d)])
    diagonals = [edge(t[0],t[2]),edge(t[1],t[3])]
    red.update(diagonals)
    old = len(names)
    fresh = [vertex('outside'+str(i)) for i in range(extra)]
    def adjacent(edges):
        out=[set() for _ in names]
        for u,v in edges: out[u].add(v); out[v].add(u)
        return out
    initial_a = adjacent(red|blue)
    assert all(not(initial_a[u]&initial_a[v]) for u,v in red|blue)
    assert all(len(initial_a[u]&initial_a[v])<=1 for u,v in combinations(range(old),2))
    cursor, attached = 0, {}
    for color, edges in enumerate((red,blue)):
        a = adjacent(edges)
        for v in range(old):
            for _ in range(2-len(a[v])):
                w=fresh[cursor]; cursor+=1
                e=edge(v,w); edges.add(e)
                attached.setdefault((color,v),[]).append(e)
    assert cursor <= extra
    nodes = 0
    for edges in (red,blue):
        a=adjacent(red|blue)
        r=[2-len(z) for z in adjacent(edges)]
        def allowed(u,v):
            return (u != v and v not in a[u] and not(a[u]&a[v])
                    and not any(a[x]&a[v] for x in a[u]))
        def fill():
            nonlocal nodes
            nodes+=1
            if nodes > 200000: return False
            todo=[v for v in fresh if r[v]]
            if not todo: return True
            # Deterministic randomized priority; the final sparse tail gets MRV.
            if len(todo) < 20:
                choices=[(u,[v for v in todo if allowed(u,v)]) for u in todo]
                u, candidates=min(choices,key=lambda item:len(item[1]))
            else:
                u=max(todo,key=lambda v:(len(a[v]),r[v],rng.random()))
                candidates=[v for v in todo if allowed(u,v)]
            rng.shuffle(candidates)
            for v in candidates:
                r[u]-=1; r[v]-=1
                a[u].add(v); a[v].add(u); edges.add(edge(u,v))
                if fill(): return True
                edges.remove(edge(u,v)); a[u].remove(v); a[v].remove(u)
                r[u]+=1; r[v]+=1
            return False
        assert fill(), ('completion failed',color,nodes)
    red=sorted(red); blue=sorted(blue)
    a=adjacent(red+blue)
    assert all(len(nb)==4 for nb in a)
    assert all(not(a[u]&a[v]) for u,v in red+blue)
    assert all(len(a[u]&a[v])<=1 for u,v in combinations(range(len(names)),2))
    h=[set() for e in red]
    for i,j in combinations(range(len(red)),2):
        e,f=red[i],red[j]
        if set(e)&set(f) or any(y in a[x] for x in e for y in f):
            h[i].add(j); h[j].add(i)
    assert all(len(nb)==12 for nb in h)
    ids={e:i for i,e in enumerate(red)}
    qids=[ids[e] for e in qs]
    rids=[[ids[e] for e in path] for path in rs]
    fixed={qids[0]:0, **{qids[i]:1 for i in (1,2,3)}}
    fixed.update({ids[e]:2 for e in diagonals})
    for path in rids:
        fixed.update({e:0 for e in path})
    fs=[]; gs=[]
    for i in range(4):
        f=attached[(0,s[i])][0]; fs.append(ids[f])
        fixed[ids[f]]=1 if i%2==0 else 2
        outside=next(v for v in f if v!=s[i])
        g=next(e for e in red if outside in e and e!=f)
        gs.append(ids[g]); fixed[ids[g]]=2
    fixedA={v for v,c in fixed.items() if c==0}
    palettes=[]
    for v in range(len(red)):
        palettes.append([fixed[v]] if v in fixed else
                        ([1,2] if h[v]&fixedA else [0,1,2]))
    return {'names':names,'red':red,'blue':blue,'h':h,'fixed':fixed,
            'palettes':palettes,'q':qids,'R':rids,'f':fs,'g':gs,
            'completion_nodes':nodes}


def search(data,seed=31871,steps=200000,exchange=False,warm=None):
    rng=random.Random(seed)
    h=data['h'];pal=[p[:] for p in data['palettes']]; n=len(h)
    caps=[4,3,3]
    targets={}
    variants=[[(None,(0,0,0))] for _ in range(n)]
    if exchange:
        targets.update({v:[4,4,4] for v in [data['q'][0]]+data['R'][0]})
        for part in data['R'][1:]: targets.update({v:[3,5,4] for v in part})
        targets.update({v:[5,3,4] for v in data['q'][1:]})
        q=data['q'][0]
        for w in data['q'][1:]:
            for v in range(n):
                shift=int(w in h[v])-int(q in h[v])
                override=1 if v==q else 0 if v==w else None
                variants[v].append((override,(shift,-shift,0)))
    changed=True
    while changed:
        changed=False
        for v in range(n):
            limits = {c:targets[v][c] for c in range(3)} if v in targets else (
                {pal[v][0]:caps[pal[v][0]]} if len(pal[v])==1 else {})
            for c,limit in limits.items():
                forced=[w for w in h[v] if pal[w]==[c]]
                possible=[w for w in h[v] if c in pal[w]]
                assert len(forced)<=limit
                if len(forced)==limit:
                    for w in set(possible)-set(forced):
                        pal[w].remove(c);changed=True
                        assert pal[w]
                if v in targets:
                    assert len(possible)>=limit
                    if len(possible)==limit:
                        for w in possible:
                            if pal[w]!=[c]: pal[w]=[c];changed=True
    colors=[warm[v] if warm is not None and warm[v] in p else rng.choice(p)
            for v,p in enumerate(pal)]
    counts=[[sum(colors[w]==c for w in nb) for c in range(3)] for nb in h]
    def cost(v):
        total=0
        for override,shift in variants[v]:
            c=colors[v] if override is None else override
            total+=sum(max(0,counts[v][c]+shift[c]-counts[v][b]-shift[b]+caps[b]-caps[c])
                       for b in range(3) if b!=c)
        if v in targets: total+=2*sum(abs(counts[v][c]-targets[v][c]) for c in range(3))
        return total
    costs=[cost(v) for v in range(n)]
    total=sum(costs); best=total; bestcolors=colors[:]
    eligible=[v for v,p in enumerate(pal) if len(p)>1]
    for step in range(steps):
        if total==0: break
        bad=rng.choice([v for v in range(n) if costs[v]])
        options=[v for v in h[bad]|{bad} if len(pal[v])>1]
        if not options: return {'best_cost':best,'colors':bestcolors,'steps':step,'blocked':bad}
        v=rng.choice(options)
        old=colors[v]; new=rng.choice([c for c in pal[v] if c!=old])
        affected=h[v]|{v}; before=sum(costs[w] for w in affected)
        colors[v]=new
        for w in h[v]: counts[w][old]-=1;counts[w][new]+=1
        changed={w:cost(w) for w in affected}
        delta=sum(changed.values())-before
        temperature=0.08+1.7*(1-(step%25000)/25000)**2
        if delta<=0 or rng.random()<math.exp(-delta/temperature):
            total+=delta
            for w,x in changed.items(): costs[w]=x
            if total<best:
                best=total;bestcolors=colors[:]
        else:
            colors[v]=old
            for w in h[v]: counts[w][new]-=1;counts[w][old]+=1
    return {'best_cost':best,'colors':bestcolors,'steps':step+1}


def main():
    extra=int(sys.argv[1]) if len(sys.argv)>1 else 80
    exchange=len(sys.argv)>2 and sys.argv[2]=='exchange'
    data=build(extra=extra)
    warm=None
    if len(sys.argv)>3:
        warm=json.loads(Path(sys.argv[3]).read_text(encoding='utf-8'))['best']['colors']
    attempts=[]; best=None
    for seed in range(31871,31877):
        result=search(data,seed,exchange=exchange,warm=warm)
        attempts.append({k:v for k,v in result.items() if k!='colors'})
        print(seed,attempts[-1],flush=True)
        if best is None or result['best_cost']<best['best_cost']: best=result
        warm=best['colors']
        if result['best_cost']==0: break
    colors=best['colors']; h=data.pop('h'); data.pop('palettes')
    counts=[[sum(colors[w]==c for w in nb) for c in range(3)] for nb in h]
    assert counts[data['q'][0]]==[4,4,4]
    assert all(counts[q]==[5,3,4] for q in data['q'][1:])
    data.update({'search':attempts,'best':best,'degrees':counts,
                 'potential':sum(colors[v]==colors[w] for v,nb in enumerate(h) for w in nb)//2
                 -sum([4,3,3][c] for c in colors),
                 'exchange_constraints':exchange,
                 'claim':'Complete G,F; local minimum only if best_cost=0. Global optimality NOT claimed.'})
    target=Path(__file__).with_suffix('.json') if extra==80 else Path(__file__).with_name(
        Path(__file__).stem+'_'+str(extra)+'.json')
    if exchange: target=target.with_name(target.stem+'_exchange.json')
    target.write_text(json.dumps(data,indent=2),encoding='utf-8')
    print('vertices',len(data['names']),'red',len(data['red']),'best_cost',best['best_cost'])


if __name__=='__main__': main()
