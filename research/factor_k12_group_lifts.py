"""Exhaust Z4 or Klein-four voltage lifts of the K12 factor example.

The base is the double-vertex blow-up of C6.  Red comprises alternating
K2,2 blocks and has complete conflict graph on its twelve edges.
"""
from itertools import combinations, permutations
from pathlib import Path
from collections import deque
import argparse
import json
from factor_double_lift_search import conflict_graph
from factor_cyclic_lift_search import ten_color


def base_model():
    red = [(2*i+x,2*((i+1)%6)+y) for i in (0,2,4) for x in range(2) for y in range(2)]
    blue = [(2*i+x,2*((i+1)%6)+y) for i in (1,3,5) for x in range(2) for y in range(2)]
    base = red+blue
    index = {tuple(sorted(e)):j for j,e in enumerate(base)}
    adj = [set() for _ in range(12)]
    for a,b in base:
        adj[a].add(b)
        adj[b].add(a)
    _,h = conflict_graph(12,base,red)
    assert all(len(ns)==11 for ns in h)
    tree = set()
    seen = {0}
    todo = deque([0])
    while todo:
        a = todo.popleft()
        for b in sorted(adj[a]):
            if b not in seen:
                seen.add(b)
                todo.append(b)
                tree.add(index[tuple(sorted((a,b)))])
    free = [j for j in range(24) if j not in tree]
    assert len(free)==13
    free_index = {j:i for i,j in enumerate(free)}
    cycles = set()
    for cyc in permutations(range(12),4):
        if all(cyc[(i+1)%4] in adj[cyc[i]] for i in range(4)):
            rev = cyc[::-1]
            cycles.add(min([cyc[i:]+cyc[:i] for i in range(4)] +
                           [rev[i:]+rev[:i] for i in range(4)]))
    forms = []
    for cyc in sorted(cycles):
        row = []
        for i,a in enumerate(cyc):
            b = cyc[(i+1)%4]
            j = index[tuple(sorted((a,b)))]
            if j in free_index:
                row.append((free_index[j],1 if base[j]==(a,b) else -1))
        forms.append(row)
    return base,free,forms


def run(group):
    base,free,forms = base_model()
    stats = {'states':0,'valid_lifts':0,'color_histogram':{},'max_color':0}
    records = []
    def add(a,b):
        return (a+b)%4 if group=='z4' else a^b
    def negate(a):
        return (-a)%4 if group=='z4' else a
    def search(dom):
        stats['states'] += 1
        changed = True
        while changed:
            changed = False
            for row in forms:
                fixed = 0
                undecided = []
                for i,sign in row:
                    if len(dom[i])==1:
                        x = next(iter(dom[i]))
                        fixed = add(fixed,x if sign==1 else negate(x))
                    else:
                        undecided.append((i,sign))
                if not undecided:
                    if fixed == 0:
                        return
                elif len(undecided)==1:
                    i,sign = undecided[0]
                    forbidden = negate(fixed) if sign==1 else fixed
                    if forbidden in dom[i]:
                        dom[i] = dom[i]-{forbidden}
                        if not dom[i]:
                            return
                        changed = True
        undecided = [(len(ds),i) for i,ds in enumerate(dom) if len(ds)>1]
        if undecided:
            _,i = min(undecided)
            for x in sorted(dom[i]):
                child = dom.copy()
                child[i] = {x}
                search(child)
            return
        voltage = [0]*24
        for j,ds in zip(free,dom):
            voltage[j] = next(iter(ds))
        gedges = [(4*a+x,4*b+add(x,voltage[j]))
                  for j,(a,b) in enumerate(base) for x in range(4)]
        factor = gedges[:48]
        g,h = conflict_graph(48,gedges,factor)
        assert all(len(ns)==4 for ns in g)
        assert all(not g[a]&g[b] for a,b in gedges)
        assert all(len(g[a]&g[b])<=1 for a,b in combinations(range(48),2))
        assert all(len(ns)==12 for ns in h)
        colors,nodes = ten_color(h)
        stats['valid_lifts'] += 1
        row = {'voltage':[voltage[j] for j in free],'colors':colors,
               'ten_color_search_nodes':nodes}
        if colors is None:
            row['G_edges'] = gedges
            row['factor'] = factor
            row['color_count'] = None
        else:
            k = max(colors)+1
            row['color_count'] = k
            stats['max_color'] = max(stats['max_color'],k)
            stats['color_histogram'][str(k)] = stats['color_histogram'].get(str(k),0)+1
            for i,j in combinations(range(48),2):
                if colors[i]==colors[j]:
                    e,f = factor[i],factor[j]
                    assert not set(e)&set(f)
                    assert not any(y in g[x] for x in e for y in f)
        records.append(row)
    search([set(range(4)) for _ in free])
    result = {'group':group,'normalized_assignments':4**len(free),
              'base_four_cycles':len(forms),'base_edges':base,
              'free_base_edges':free,'stats':stats,'certificates':records}
    Path(f'research/factor_k12_{group}.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('base_edges','certificates')}),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('group',choices=('z4','v4'))
    run(parser.parse_args().group)
