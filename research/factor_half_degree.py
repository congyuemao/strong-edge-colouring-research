"""Exact two-part maximum-internal-degree-five test on a supplied factor.

The search has no cutoff. A successful partition is an endpoint-checkable
certificate. Exhaustion rules out this stronger partition, not ten-coloring.
"""
import json
from pathlib import Path


def original_example():
    n = 25
    red = [(5*i+j, 5*i+(j+1)%5) for i in range(5) for j in range(5)]
    blue = [(5*i+j, 5*((i+1)%5)+(2*j)%5)
            for i in range(5) for j in range(5)]
    return n, red, blue


def build(n, red, blue):
    adj = [set() for _ in range(n)]
    for u,v in red+blue:
        adj[u].add(v)
        adj[v].add(u)
    assert all(len(s)==4 for s in adj)
    assert all(not(adj[u]&adj[v]) for u,v in red+blue)
    assert all(len(adj[u]&adj[v])<=1 for u in range(n) for v in range(u))
    h = [set() for _ in red]
    for i,(u,v) in enumerate(red):
        for j,(x,y) in enumerate(red[:i]):
            if {u,v}&{x,y} or any(b in adj[a] for a in (u,v) for b in (x,y)):
                h[i].add(j)
                h[j].add(i)
    assert all(len(s)==12 for s in h)
    return h


def solve(h):
    nodes = 0
    def visit(state):
        nonlocal nodes
        nodes += 1
        again = True
        while again:
            again = False
            for v,nb in enumerate(h):
                counts = [sum(state[w]==c for w in nb) for c in (0,1)]
                if state[v] < 0:
                    if counts[0]>5 and counts[1]>5:
                        return None
                    if max(counts)>5:
                        state[v] = 1 if counts[0]>5 else 0
                        again = True
                if state[v] >= 0:
                    c = state[v]
                    if counts[c]>5:
                        return None
                    if counts[c]==5:
                        for w in nb:
                            if state[w]<0:
                                state[w] = 1-c
                                again = True
        free = [v for v in range(len(h)) if state[v]<0]
        if not free:
            return state
        v = max(free,key=lambda x:sum(state[w]>=0 for w in h[x]))
        for c in (0,1):
            nxt = state[:]
            nxt[v] = c
            ans = visit(nxt)
            if ans is not None:
                return ans
        return None
    state = [-1]*len(h)
    state[0] = 0  # interchange of the two parts preserves every constraint
    answer = visit(state)
    return answer,nodes


def main():
    n,red,blue = original_example()
    h = build(n,red,blue)
    answer,nodes = solve(h)
    result = {'vertices':n,'red_edges':red,'blue_edges':blue,
              'partition':answer,'search_nodes':nodes,
              'statement':'existence of a (5,5) internal-degree partition'}
    if answer is not None:
        degrees = [sum(answer[u]==answer[v] for u in h[v]) for v in range(n)]
        assert max(degrees)<=5
        result['internal_degrees'] = degrees
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({'found':answer is not None,'search_nodes':nodes,
                     'internal_degrees':result.get('internal_degrees')}))


if __name__ == '__main__':
    main()
