"""Exact endpoint search for the eight classified high-clique cores."""
from itertools import combinations, permutations
from pathlib import Path
import json


def realize(item):
    n = item['n']
    h = [set() for _ in range(n)]
    for u,v in item['edges']:
        h[u].add(v)
        h[v].add(u)
    options = []
    for ns in h:
        ns = sorted(ns)
        options.append([frozenset((ns[0],)+sub)
                        for size in range(len(ns))
                        for sub in combinations(ns[1:],size)
                        if size+1 <= 3 and len(ns)-size-1 <= 3])
    allowed = {}
    for u in range(n):
        for v in h[u]:
            masks = []
            for pu in options[u]:
                masks.append(sum(1 << j for j,pv in enumerate(options[v])
                    if all(not (((v in pu) == (w in pu)) and
                                ((u in pv) == (w in pv))) for w in h[u]&h[v])))
            allowed[u,v] = masks
    cycles = set()
    for a,b,c,d in permutations(range(n),4):
        if b in h[a] and c in h[b] and d in h[c] and a in h[d]:
            cyc = (a,b,c,d)
            rev = cyc[::-1]
            cycles.add(min([cyc[i:]+cyc[:i] for i in range(4)] +
                           [rev[i:]+rev[:i] for i in range(4)]))
    clauses = []
    for cyc in cycles:
        clauses.append((cyc, [sum(1 << j for j,p in enumerate(options[u])
            if (cyc[i-1] in p) != (cyc[(i+1)%4] in p)) for i,u in enumerate(cyc)]))
    nodes = 0
    def search(dom):
        nonlocal nodes
        nodes += 1
        changed = True
        while changed:
            changed = False
            for (u,v), masks in allowed.items():
                new = sum(1 << k for k in range(len(options[u]))
                          if dom[u] >> k & 1 and masks[k] & dom[v])
                if not new:
                    return None
                if new != dom[u]:
                    dom[u] = new
                    changed = True
            for cyc,masks in clauses:
                if any(dom[u] & ~mask == 0 for u,mask in zip(cyc,masks)):
                    continue
                possible = [(u,mask) for u,mask in zip(cyc,masks) if dom[u]&mask]
                if not possible:
                    return None
                if len(possible) == 1:
                    u,mask = possible[0]
                    new = dom[u]&mask
                    if new != dom[u]:
                        dom[u] = new
                        changed = True
        undecided = [(d.bit_count(),u) for u,d in enumerate(dom) if d.bit_count()>1]
        if not undecided:
            return [d.bit_length()-1 for d in dom]
        _,u = min(undecided)
        for j in range(len(options[u])):
            if dom[u] >> j & 1:
                child = dom.copy()
                child[u] = 1 << j
                answer = search(child)
                if answer is not None:
                    return answer
        return None
    answer = search([(1 << len(p))-1 for p in options])
    result = {'n':n, 'high_points':item['high_points'], 'states':nodes,
              'found':answer is not None}
    if answer is None:
        return result
    gedges = [(2*u,2*u+1) for u in range(n)]
    for u,v in item['edges']:
        gedges.append((2*u+int(v not in options[u][answer[u]]),
                       2*v+int(u not in options[v][answer[v]])))
    g = [set() for _ in range(2*n)]
    for u,v in gedges:
        g[u].add(v)
        g[v].add(u)
    assert max(map(len,g)) <= 4
    assert all(not g[u]&g[v] for u,v in gedges)
    assert all(len(g[u]&g[v]) <= 1 for u,v in combinations(range(2*n),2))
    for u,v in combinations(range(n),2):
        clash = any(y in g[x] for x in (2*u,2*u+1) for y in (2*v,2*v+1))
        assert clash == (v in h[u])
    result['G_edges'] = gedges
    result['degrees'] = list(map(len,g))
    result['port_zero'] = [sorted(options[u][answer[u]]) for u in range(n)]
    return result


if __name__ == '__main__':
    source = json.loads(Path('research/four_critical_high_clique.json').read_text())
    results = [realize(item) for item in source['classes']]
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(results,indent=2),encoding='utf-8')
    print(json.dumps([{k:v for k,v in item.items() if k not in
                      ('G_edges','degrees','port_zero')} for item in results]))
