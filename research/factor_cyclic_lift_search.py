"""Exhaust normalized cyclic-voltage lifts of the 11-color factor example.

All arithmetic is integral.  Each surviving lift has an explicit coloring
certificate checked against original endpoints, not only a derived matrix.
"""
from itertools import combinations, permutations
from pathlib import Path
import argparse
import json
from factor_double_lift_search import conflict_graph, greedy


def base_model():
    base = [(i,(i+1)%11) for i in range(11)] + [(i,(i+4)%11) for i in range(11)]
    index = {tuple(sorted(e)):j for j,e in enumerate(base)}
    adj = [set() for _ in range(11)]
    for a,b in base:
        adj[a].add(b)
        adj[b].add(a)
    cycles = set()
    for seq in permutations(range(11),4):
        if all(seq[(i+1)%4] in adj[seq[i]] for i in range(4)):
            rev = seq[::-1]
            cycles.add(min([seq[i:]+seq[:i] for i in range(4)] +
                           [rev[i:]+rev[:i] for i in range(4)]))
    forms = []
    for cyc in sorted(cycles):
        row = []
        for i,a in enumerate(cyc):
            b = cyc[(i+1)%4]
            j = index[tuple(sorted((a,b)))]
            if j >= 10:
                row.append((j-10, 1 if base[j] == (a,b) else -1))
        forms.append(row)
    return base,forms


def ten_color(h):
    colors = greedy(h)
    if max(colors) < 10:
        return colors, 0
    colors = [-1]*len(h)
    visits = 0
    def search(left,used):
        nonlocal visits
        visits += 1
        if not left:
            return colors[:]
        v = max((v for v in range(len(h)) if colors[v] < 0),
                key=lambda v:(len({colors[w] for w in h[v] if colors[w]>=0}),
                              sum(colors[w]<0 for w in h[v])))
        forbidden = {colors[w] for w in h[v] if colors[w]>=0}
        for c in range(min(10,used+1)):
            if c not in forbidden:
                colors[v] = c
                result = search(left-1,max(used,c+1))
                if result is not None:
                    return result
                colors[v] = -1
        return None
    return search(len(h),0),visits


def run(p):
    base,forms = base_model()
    values = [-1]*12
    records = []
    states = 0
    def search(dom):
        nonlocal states
        states += 1
        changed = True
        while changed:
            changed = False
            for row in forms:
                fixed = sum(sign*next(iter(dom[i])) for i,sign in row if len(dom[i])==1)%p
                free = [(i,sign) for i,sign in row if len(dom[i])>1]
                if not free:
                    if fixed == 0:
                        return
                elif len(free)==1:
                    i,sign = free[0]
                    forbidden = (-sign*fixed)%p
                    if forbidden in dom[i]:
                        dom[i] = dom[i]-{forbidden}
                        if not dom[i]:
                            return
                        changed = True
        remaining = [(len(ds),i) for i,ds in enumerate(dom) if len(ds)>1]
        if remaining:
            _,i = min(remaining)
            for x in sorted(dom[i]):
                child = dom.copy()
                child[i] = {x}
                search(child)
            return
        voltage = [next(iter(ds)) for ds in dom]
        gedges = []
        for j,(a,b) in enumerate(base):
            shift = voltage[j-10] if j>=10 else 0
            gedges.extend((p*a+x,p*b+(x+shift)%p) for x in range(p))
        factor = gedges[:11*p]
        g,h = conflict_graph(11*p,gedges,factor)
        assert all(len(ns)==4 for ns in g)
        assert all(not g[a]&g[b] for a,b in gedges)
        assert all(len(g[a]&g[b])<=1 for a,b in combinations(range(11*p),2))
        assert all(len(ns)==12 for ns in h)
        colors,nodes = ten_color(h)
        row = {'voltages':voltage,'ten_color_search_nodes':nodes,
               'coloring':colors,'number_of_colors':max(colors)+1 if colors else None}
        if colors is None:
            row['G_edges'] = gedges
            row['factor_edges'] = factor
        else:
            for i,j in combinations(range(len(factor)),2):
                e,f = factor[i],factor[j]
                if set(e)&set(f) or any(y in g[x] for x in e for y in f):
                    assert colors[i]!=colors[j]
        records.append(row)
    search([set(range(p)) for _ in range(12)])
    result = {'modulus':p,'all_normalized_assignments':p**12,
              'constraint_search_states':states,'base_edges':base,
              'valid_girth_five_lifts':len(records),'certificates':records}
    Path(f'research/factor_cyclic_lift_{p}.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('base_edges','certificates')}))
    print(json.dumps({'colors':{str(k):sum(r['number_of_colors']==k for r in records)
        for k in sorted({r['number_of_colors'] for r in records},key=lambda x:-1 if x is None else x)}}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('modulus',type=int,default=3,nargs='?')
    args = parser.parse_args()
    run(args.modulus)
