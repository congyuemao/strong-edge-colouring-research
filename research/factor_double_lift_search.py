"""Exhaust every two-sheet lift of the known eleven-color factor example.

Switching at the eleven fibers normalizes a red spanning path to voltage 0.
The remaining twelve binary voltages are exhausted.  All factor conflicts
are checked in the full lifted original graph.
"""
from itertools import combinations, permutations
from pathlib import Path
import json


def conflict_graph(n, edges, factor):
    g = [set() for _ in range(n)]
    for a,b in edges:
        g[a].add(b)
        g[b].add(a)
    h = [set() for _ in factor]
    for i,j in combinations(range(len(factor)),2):
        e,f = factor[i],factor[j]
        if set(e)&set(f) or any(y in g[x] for x in e for y in f):
            h[i].add(j)
            h[j].add(i)
    return g,h


def greedy(h):
    colors = [-1]*len(h)
    for _ in h:
        v = max((u for u in range(len(h)) if colors[u] < 0),
                key=lambda u:(len({colors[w] for w in h[u] if colors[w]>=0}),
                              len(h[u])))
        used = {colors[w] for w in h[v]}
        colors[v] = next(c for c in range(len(h)+1) if c not in used)
    return colors


def main():
    red = [(i,(i+1)%11) for i in range(11)]
    blue = [(i,(i+4)%11) for i in range(11)]
    base = red+blue
    base_index = {tuple(sorted(e)):i for i,e in enumerate(base)}
    adj = [set() for _ in range(11)]
    for a,b in base:
        adj[a].add(b)
        adj[b].add(a)
    cycles = set()
    for a,b,c,d in permutations(range(11),4):
        if b in adj[a] and c in adj[b] and d in adj[c] and a in adj[d]:
            cycles.add(tuple(sorted(base_index[tuple(sorted(e))] for e in
                                   ((a,b),(b,c),(c,d),(d,a)))))
    equations = [sum(1 << (j-10) for j in cyc if j>=10) for cyc in cycles]
    records = []
    for mask in range(1 << 12):
        if not all((mask & eq).bit_count()%2 for eq in equations):
            continue
        edges = []
        for j,(a,b) in enumerate(base):
            voltage = (mask >> (j-10))&1 if j>=10 else 0
            for x in range(2):
                edges.append((2*a+x,2*b+(x^voltage)))
        factor = edges[:22]
        g,h = conflict_graph(22,edges,factor)
        assert all(len(a)==4 for a in g)
        assert all(not g[a]&g[b] for a,b in edges)
        assert all(len(g[a]&g[b])<=1 for a,b in combinations(range(22),2))
        assert all(len(a)==12 for a in h)
        colors = greedy(h)
        assert max(colors)<10
        assert all(colors[i]!=colors[j] for i in range(22) for j in h[i])
        records.append({'voltage_mask':mask,'colors':colors,
                        'number_of_colors':max(colors)+1,
                        'G_edges':edges,'factor_edges':factor})
    result = {'normalized_voltages_checked':1<<12, 'base_four_cycles':len(cycles),
              'valid_lifts':len(records),'certificates':records}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='certificates'}))
    print(json.dumps({'color_distribution':{str(k):sum(x['number_of_colors']==k
        for x in records) for k in sorted({x['number_of_colors'] for x in records})}}))


if __name__ == '__main__':
    main()
