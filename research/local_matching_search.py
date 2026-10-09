"""Exhaustive local obstruction search; no third-party packages.

Does a triangle-free maximum-degree-four graph, with every edge in at
most one 4-cycle, have a radius-two boundary with no induced 3-matching
at a vertex belonging to two 4-cycles?  A returned UNSAT exhausts all
possible edges between radius-two vertices; vertices farther away
cannot change conflicts between boundary edges.
"""
from itertools import combinations
import json
from pathlib import Path


def run():
    # 0 is root; 1,2,3,4 its neighbours; 5 joins 1,2; 6 joins 3,4.
    groups = {1: [5, 7, 8], 2: [5, 9, 10],
              3: [6, 11, 12], 4: [6, 13, 14]}
    boundary = [(a, x) for a, xs in groups.items() for x in xs]
    base = [(0, a) for a in groups] + boundary
    supports = {x: {a for a, xs in groups.items() if x in xs}
                for x in range(5, 15)}
    possible = [(x, y) for x, y in combinations(range(5, 15), 2)
                if not supports[x] & supports[y]]
    edge_index = {e: i for i, e in enumerate(possible)}
    clauses = set()
    for es in combinations(boundary, 3):
        pairs = list(combinations(es, 2))
        if any(a == b or x == y or a in supports[y] or b in supports[x]
               for (a, x), (b, y) in pairs):
            continue
        clauses.add(sum(1 << edge_index[tuple(sorted((x, y)))]
                        for (_, x), (_, y) in pairs))
    clauses = sorted(clauses)
    adj = [set() for _ in range(15)]
    for x, y in base:
        adj[x].add(y)
        adj[y].add(x)
    seen = set()
    stats = {"states": 0, "capacity_prunes": 0,
             "triangle_prunes": 0, "four_cycle_prunes": 0}

    def valid_add(x, y):
        if len(adj[x]) == 4 or len(adj[y]) == 4:
            stats["capacity_prunes"] += 1
            return False
        if adj[x] & adj[y]:
            stats["triangle_prunes"] += 1
            return False
        adj[x].add(y)
        adj[y].add(x)
        # Number of 4-cycles containing uv is the number of cross
        # edges between N(u)-v and N(v)-u (triangle freedom holds).
        ok = True
        for u in range(15):
            for v in adj[u]:
                if v < u:
                    continue
                count = sum(b in adj[a] for a in adj[u] - {v}
                            for b in adj[v] - {u})
                if count > 1:
                    ok = False
                    break
            if not ok:
                break
        adj[x].remove(y)
        adj[y].remove(x)
        if not ok:
            stats["four_cycle_prunes"] += 1
        return ok

    def search(selected):
        if selected in seen:
            return None
        seen.add(selected)
        stats["states"] += 1
        uncovered = [c for c in clauses if not c & selected]
        if not uncovered:
            return [possible[i] for i in range(len(possible))
                    if selected >> i & 1]
        # Invalid additions stay invalid under further additions.
        best = None
        for clause in uncovered:
            opts = []
            while clause:
                bit = clause & -clause
                clause -= bit
                i = bit.bit_length() - 1
                if valid_add(*possible[i]):
                    opts.append(i)
            if not opts:
                return None
            if best is None or len(opts) < len(best):
                best = opts
                if len(best) == 1:
                    break
        for i in best:
            x, y = possible[i]
            adj[x].add(y)
            adj[y].add(x)
            answer = search(selected | (1 << i))
            adj[x].remove(y)
            adj[y].remove(x)
            if answer is not None:
                return answer
        return None

    answer = search(0)
    result = {"result": "UNSAT" if answer is None else "SAT",
              "potential_edges": len(possible),
              "induced_matching_clauses": len(clauses),
              "stats": stats, "completion_edges": answer}
    print(json.dumps(result, indent=2))
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(result, indent=2), encoding="utf-8")


if __name__ == "__main__":
    run()
