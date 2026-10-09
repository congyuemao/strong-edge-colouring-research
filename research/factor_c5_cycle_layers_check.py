"""Direct endpoint certificates for the pure C5 circle-chain coloring.

The proof is in factor_c5_cycle_layers.md.  This code tests representatives
of every affine return-map type for lengths 3 through 12; it is not an
exhaustive test of arbitrary graphs or a replacement for that proof.
"""
from itertools import combinations
from pathlib import Path
import json


def cycles(perm):
    unseen = set(range(5))
    answer = []
    while unseen:
        start = min(unseen)
        cycle = [start]
        unseen.remove(start)
        v = perm[start]
        while v != start:
            cycle.append(v)
            unseen.remove(v)
            v = perm[v]
        if len(cycle) > 1:
            answer.append(cycle)
    return answer


def color_rows(m, perm):
    row = list(range(5))
    rows = [row.copy()]
    cs = cycles(perm)
    if m == 4:
        assert len(cs) == 1 and len(cs[0]) == 5
        a = cs[0]
        updates = [
            [(a[0],5),(a[2],6)],
            [(a[4],a[0]),(a[1],a[2])],
            [(a[3],a[4]),(a[0],a[1])],
            [(a[2],a[3])]]
    else:
        updates = []
        for a in cs:
            updates.append([(a[0],5)])
            for i in range(len(a)-1,0,-1):
                updates.append([(a[i],a[(i+1)%len(a)])])
            updates.append([(a[0],a[1])])
        assert len(updates) <= m
        updates += [[]]*(m-len(updates))
    for change in updates:
        assert all(c not in row for _,c in change)
        assert len({v for v,_ in change}) == len(change)
        for v,c in change:
            row[v] = c
        assert len(set(row)) == 5
        rows.append(row.copy())
    assert len(rows) == m+1
    assert rows[-1] == perm
    return rows[:-1]


def check(m, last_a, last_b):
    maps = [(2,0)]*(m-1)+[(last_a,last_b)]
    red = [(5*i+j,5*i+(j+1)%5) for i in range(m) for j in range(5)]
    blue = [(5*i+j,5*((i+1)%m)+(a*j+b)%5)
            for i,(a,b) in enumerate(maps) for j in range(5)]
    g = [set() for _ in range(5*m)]
    for u,v in red+blue:
        g[u].add(v)
        g[v].add(u)
    assert all(len(ns) == 4 for ns in g)
    high_girth = (all(not g[u]&g[v] for u,v in red+blue)
                  and all(len(g[u]&g[v]) <= 1
                          for u,v in combinations(range(5*m),2)))
    prefixes = [list(range(5))]
    for a,b in maps:
        prefixes.append([(a*x+b)%5 for x in prefixes[-1]])
    perm = prefixes[-1]
    result = {'m':m,'last_map':[last_a,last_b],'return':perm,
              'high_girth':high_girth}
    if not high_girth:
        assert m <= 4
        return result
    rows = color_rows(m,perm)
    color = [rows[i][prefixes[i].index((j+3)%5)]
             for i in range(m) for j in range(5)]
    for p,q in combinations(range(5*m),2):
        if color[p] == color[q]:
            e,f = red[p],red[q]
            assert not set(e)&set(f)
            assert not any(y in g[x] for x in e for y in f)
    result['color_count'] = len(set(color))
    result['colors'] = color
    return result


if __name__ == '__main__':
    result = [check(m,a,b) for m in range(3,13)
              for a in (2,3) for b in range(5)]
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    valid = [r for r in result if r['high_girth']]
    print(json.dumps({'tested':len(result),'valid':len(valid),
        'color_histogram':{str(k):sum(r['color_count']==k for r in valid)
                           for k in (5,6,7)}}))
