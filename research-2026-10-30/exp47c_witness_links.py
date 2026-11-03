"""exp47c: how much an exp47 witness leans on the port relaxation (NEW_DIRECTIONS 11.17).

For every centre (e and each singleton member f_p) and every colour pair (a, b) (p not in {a, b}) the pair is linked in
the witness under the relaxation.  This script sorts the links by how they come about:
  inside  -- one (a, b)-component inside the ball meets both an a-member and a b-member of the centre;
  port    -- linked only because an a-member and a b-member each lie in a component that reaches the boundary
             (L2-distance 3 from e, or R for a ball of radius R).
It also reports, for the inside links, the largest L2-distance from e reached by the linking component.
Conflicts, distances and components are recomputed from the vertex sets (same conventions as exp47b).
Usage: exp47c_witness_links.py <witness.json>
"""
import json
import sys
from collections import Counter, deque

w = json.load(open(sys.argv[1], encoding="utf-8"))
edges, col = [tuple(x) for x in w["edges"]], w["col"]
K, e, m = 20, 0, len(edges)
nb, inc = {}, {}
for i, (x, y) in enumerate(edges):
    nb.setdefault(x, set()).add(y)
    nb.setdefault(y, set()).add(x)
    inc.setdefault(x, []).append(i)
    inc.setdefault(y, []).append(i)
conf = []
for i, (x, y) in enumerate(edges):
    near = {x, y} | nb[x] | nb[y]
    conf.append(sorted({j for v in near for j in inc[v]} - {i}))
dist = {e: 0}
q = deque([e])
while q:
    h = q.popleft()
    for g in conf[h]:
        if g not in dist:
            dist[g] = dist[h] + 1
            q.append(g)
R = max(dist.values())
N = conf[e]
mult = Counter(col[f] for f in N if col[f] >= 0)
centres = [(e, -1)] + [(f, col[f]) for f in N if mult[col[f]] == 1]


def comps(a, b):
    lab, out = {}, []
    for s in range(m):
        if s in lab or col[s] not in (a, b):
            continue
        comp, stack = [s], [s]
        lab[s] = len(out)
        while stack:
            x = stack.pop()
            for y in conf[x]:
                if y not in lab and col[y] in (a, b):
                    lab[y] = len(out)
                    comp.append(y)
                    stack.append(y)
        out.append(comp)
    return lab, out


kinds = {"e": Counter(), "members": Counter()}
reach = Counter()
for a in range(K):
    for b in range(a + 1, K):
        lab, cs = comps(a, b)
        border = [any(dist[h] == R for h in c) for c in cs]
        for c, p in centres:
            if p in (a, b):
                continue
            A = {lab[g] for g in conf[c] if col[g] == a}
            B = {lab[g] for g in conf[c] if col[g] == b}
            if A & B:
                kind = "inside"
                reach[max(dist[h] for i in A & B for h in cs[i])] += 1
            elif any(border[i] for i in A) and any(border[i] for i in B):
                kind = "port"
            else:
                kind = "SEPARABLE"
            kinds["e" if c == e else "members"][kind] += 1
print("links at e:", dict(kinds["e"]))
print("links at the singleton members:", dict(kinds["members"]))
print("inside links by the largest L2-distance from e reached by the linking component:", dict(sorted(reach.items())))
