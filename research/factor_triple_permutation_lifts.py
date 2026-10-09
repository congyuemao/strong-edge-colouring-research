"""All three-sheet permutation lifts of the eleven-color factor base.

Every permutation of three fibers is x -> s*x+b over F3.  A lifted base
four-cycle has no four-cycle above it iff its monodromy is a nontrivial
translation: its sign is positive and its translation is nonzero.
"""
from itertools import combinations, permutations
from pathlib import Path
import json
from factor_double_lift_search import conflict_graph
from factor_cyclic_lift_search import ten_color


def main():
    base = [(i,(i+1)%11) for i in range(11)] + [(i,(i+4)%11) for i in range(11)]
    index = {tuple(sorted(e)):j for j,e in enumerate(base)}
    adj = [set() for _ in range(11)]
    for a,b in base:
        adj[a].add(b)
        adj[b].add(a)
    cycles = set()
    for cyc in permutations(range(11),4):
        if all(cyc[(i+1)%4] in adj[cyc[i]] for i in range(4)):
            rev = cyc[::-1]
            cycles.add(min([cyc[i:]+cyc[:i] for i in range(4)] +
                           [rev[i:]+rev[:i] for i in range(4)]))
    paths = []
    for cyc in sorted(cycles):
        paths.append([(index[tuple(sorted((a,cyc[(i+1)%4])))],
                       base[index[tuple(sorted((a,cyc[(i+1)%4])))]] == (a,cyc[(i+1)%4]))
                      for i,a in enumerate(cyc)])
    signmasks = []
    for mask in range(1<<12):
        if all(sum((mask>>(j-10))&1 for j,_ in path if j>=10)%2 == 0
               for path in paths):
            signmasks.append(mask)
    records = []
    statistics = []
    for signmask in signmasks:
        signs = [1]*10 + [-1 if signmask>>j&1 else 1 for j in range(12)]
        forms = []
        for path in paths:
            coeff = [0]*12
            sign = 1
            for j,forward in path:
                s = signs[j]
                sign *= s
                coeff = [(s*x)%3 for x in coeff]
                if j>=10:
                    coeff[j-10] = (coeff[j-10]+(1 if forward else -s))%3
            assert sign == 1
            forms.append([(i,c) for i,c in enumerate(coeff) if c])
        states = 0
        before = len(records)
        def search(dom):
            nonlocal states
            states += 1
            changed = True
            while changed:
                changed = False
                for row in forms:
                    fixed = sum(c*next(iter(dom[i])) for i,c in row if len(dom[i])==1)%3
                    free = [(i,c) for i,c in row if len(dom[i])>1]
                    if not free:
                        if fixed == 0:
                            return
                    elif len(free)==1:
                        i,c = free[0]
                        forbidden = (-c*fixed)%3 # c is its own inverse in F3
                        if forbidden in dom[i]:
                            dom[i] = dom[i]-{forbidden}
                            if not dom[i]:
                                return
                            changed = True
            free = [(len(ds),i) for i,ds in enumerate(dom) if len(ds)>1]
            if free:
                _,i = min(free)
                for x in sorted(dom[i]):
                    child = dom.copy()
                    child[i] = {x}
                    search(child)
                return
            shifts = [0]*10+[next(iter(ds)) for ds in dom]
            gedges = [(3*a+x,3*b+(signs[j]*x+shifts[j])%3)
                      for j,(a,b) in enumerate(base) for x in range(3)]
            factor = gedges[:33]
            g,h = conflict_graph(33,gedges,factor)
            assert all(len(ns)==4 for ns in g)
            assert all(not g[a]&g[b] for a,b in gedges)
            assert all(len(g[a]&g[b])<=1 for a,b in combinations(range(33),2))
            assert all(len(ns)==12 for ns in h)
            colors,nodes = ten_color(h)
            item = {'sign_mask':signmask,'shifts':shifts[10:],
                    'colors':colors,'color_count':max(colors)+1 if colors else None,
                    'ten_color_search_nodes':nodes}
            if colors is None:
                item['G_edges'] = gedges
                item['factor'] = factor
            else:
                for i,j in combinations(range(33),2):
                    e,f = factor[i],factor[j]
                    if set(e)&set(f) or any(y in g[x] for x in e for y in f):
                        assert colors[i]!=colors[j]
            records.append(item)
        search([set(range(3)) for _ in range(12)])
        statistics.append({'sign_mask':signmask,'search_states':states,
                           'valid_lifts':len(records)-before})
    result = {'normalized_permutation_assignments':6**12,
              'admissible_sign_patterns':len(signmasks),'statistics':statistics,
              'valid_girth_five_lifts':len(records),'base_edges':base,
              'certificates':records}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('base_edges','certificates')}))
    print(json.dumps({'colors':{str(k):sum(r['color_count']==k for r in records)
        for k in sorted({r['color_count'] for r in records},key=lambda x:-1 if x is None else x)}}))


if __name__ == '__main__':
    main()
