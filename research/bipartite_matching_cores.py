"""Orient the nine classified 4-critical cores as bipartite matching conflicts.

Every orientation u->v becomes an original edge u_L v_R, and every vertex
has its matching edge u_L u_R.  This is only a realizability check, not a
proof about complete optimal degree partitions.
"""
from itertools import combinations
from pathlib import Path
import json


def solve(item):
    n = item['n']
    edges = [tuple(e) for e in item['edges']]
    adj = [set() for _ in range(n)]
    for a,b in edges:
        adj[a].add(b)
        adj[b].add(a)
    orientation = []
    left = [set([i]) for i in range(n)]
    right = [set([i]) for i in range(n)]
    states = 0

    def visit(j):
        nonlocal states
        states += 1
        if j == len(edges):
            return True
        a,b = edges[j]
        for u,v in ((a,b),(b,a)):
            if len(left[u]) == 4 or len(right[v]) == 4:
                continue
            # Adding u_L v_R creates C4 iff an existing u_L-x_R-y_L-v_R
            # path exists; the matching edges are included from the start.
            if any(right[x] & right[v] for x in left[u]):
                continue
            left[u].add(v)
            right[v].add(u)
            orientation.append((u,v))
            if visit(j+1):
                return True
            orientation.pop()
            left[u].remove(v)
            right[v].remove(u)
        return False

    found = visit(0)
    result = {'n':n, 'high_points':item['high_points'],
              'found':found, 'states':states}
    if found:
        gedges = [(2*i,2*i+1) for i in range(n)]
        gedges += [(2*u,2*v+1) for u,v in orientation]
        g = [set() for _ in range(2*n)]
        for a,b in gedges:
            g[a].add(b)
            g[b].add(a)
        assert max(map(len,g)) <= 4
        assert all((a+b)%2 == 1 for a,b in gedges)
        assert all(len(g[a]&g[b]) <= 1 for a,b in combinations(range(2*n),2))
        assert all((b in adj[a]) == any(y in g[x]
            for x in (2*a,2*a+1) for y in (2*b,2*b+1))
            for a,b in combinations(range(n),2))
        result.update(orientation=orientation,G_edges=gedges)
    return result


if __name__ == '__main__':
    source = json.loads(Path('research/four_critical_high_clique.json').read_text())
    moser = {'n':7,'high_points':1,'edges':[
        (1,2),(1,3),(2,3),(4,5),(4,6),(5,6),(1,4),
        (0,2),(0,3),(0,5),(0,6)]}
    results = [solve(item) for item in [moser]+source['classes']]
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(results,indent=2),encoding='utf-8')
    print(json.dumps([{k:v for k,v in item.items() if k not in
        ('orientation','G_edges')} for item in results]))
