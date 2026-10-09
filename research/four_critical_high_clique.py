"""Finite block-palette classification with two or three high clique points.

The accompanying mathematical reduction restricts the low-block tree to four
nodes, each an ordinary vertex or a triangle.  This enumerates that reduced
model, not unrestricted graphs on successively larger numbers of vertices.
"""
from itertools import combinations, permutations, product
from pathlib import Path
import json


def colorable(adj, deleted=-1):
    n = len(adj)
    colors = [-1]*n
    if deleted >= 0:
        colors[deleted] = 3
    def visit(left):
        if left == 0:
            return True
        options = []
        for v in range(n):
            if colors[v] < 0:
                forbidden = {colors[w] for w in adj[v] if 0 <= colors[w] < 3}
                options.append((len(forbidden), len(adj[v]), v, forbidden))
        _, _, v, forbidden = max(options, key=lambda a:a[:3])
        for c in range(3):
            if c not in forbidden:
                colors[v] = c
                if visit(left-1):
                    return True
                colors[v] = -1
        return False
    return visit(n-(deleted >= 0))


def canonical(types, tree, edgecolors, t):
    signatures = []
    for p in permutations(range(4)):
        ty = [None]*4
        for v in range(4):
            ty[p[v]] = types[v]
        for cs in permutations(range(t)):
            cmap = dict(enumerate(cs))
            if t == 2:
                cmap[2] = 2
            es = tuple(sorted((*sorted((p[u], p[v])), cmap[c])
                              for (u,v),c in zip(tree,edgecolors)))
            signatures.append((tuple(ty), es))
    return min(signatures)


def realize(types, tree, edgecolors, t):
    incident = [[] for _ in range(4)]
    for j,(u,v) in enumerate(tree):
        incident[u].append(j)
        incident[v].append(j)
    attach = []
    for i in range(4):
        cs = [edgecolors[j] for j in incident[i]]
        if types[i]:
            if len(set(cs)) != 1:
                return None
            color = cs[0]
            if len(cs) < 3 and color >= t:
                return None
            attach.append([color]*(3-len(cs)))
        else:
            if len(set(cs)) != len(cs):
                return None
            missing = [c for c in range(3) if c not in cs]
            if any(c >= t for c in missing):
                return None
            attach.append(missing)
    if any(sum(a.count(c) for a in attach) != 5-t for c in range(t)):
        return None
    nodes = []
    n = t
    for ty in types:
        nodes.append(list(range(n,n+(3 if ty else 1))))
        n += 3 if ty else 1
    edges = set(combinations(range(t),2))
    for ty, ns in zip(types,nodes):
        if ty:
            edges.update(combinations(ns,2))
    for j,(u,v) in enumerate(tree):
        a = nodes[u][incident[u].index(j) if types[u] else 0]
        b = nodes[v][incident[v].index(j) if types[v] else 0]
        edges.add(tuple(sorted((a,b))))
    for i in range(4):
        ns = nodes[i][len(incident[i]):] if types[i] else nodes[i]*len(attach[i])
        for low, high in zip(ns,attach[i]):
            edges.add((high,low))
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert [len(a) for a in adj] == [4]*t + [3]*(n-t)
    if any(all(v in adj[u] for u,v in combinations(q,2))
           for q in combinations(range(n),4)):
        return None
    assert not colorable(adj)
    assert all(colorable(adj, v) for v in range(n))
    return {'high_points': t, 'types': types, 'tree': tree,
            'tree_colors': edgecolors, 'n': n, 'edges': sorted(edges)}


def main():
    classes = []
    for t in (2,3):
        seen = set()
        for tree in ([(0,1),(1,2),(2,3)], [(0,1),(0,2),(0,3)]):
            for types in product(range(2),repeat=4):
                for cs in product(range(3),repeat=3):
                    item = realize(types,tree,cs,t)
                    if item is None:
                        continue
                    key = canonical(types,tree,cs,t)
                    if key not in seen:
                        seen.add(key)
                        classes.append(item)
    result = {'classes': classes, 'counts': {
        str(t): sum(x['high_points'] == t for x in classes) for t in (2,3)}}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
