"""Exact port-splitting search for an explicit abstract six-colour obstacle.

J has vertex set Z_11, differences +-1,+-4. H=complement(J) has degree six.
Each H vertex is split into a matched pair, with its six incident witnesses
partitioned 3+3. Test whether the resulting quartic graph can have girth >=5.
Only the standard library is used. The final graph is checked directly.
"""

from itertools import combinations, permutations
from pathlib import Path
import json


def build():
    n = 11
    j = [{(u + d) % n for d in (1, 4, 7, 10)} for u in range(n)]
    h = [set(range(n)) - {u} - j[u] for u in range(n)]
    options = []
    for u in range(n):
        neighbors = sorted(h[u])
        options.append([frozenset((neighbors[0],) + p)
                        for p in combinations(neighbors[1:], 2)])
    assert all(len(o) == 10 for o in options)
    allowed = {}
    for u in range(n):
        for v in h[u]:
            masks = []
            common = h[u] & h[v]
            for pu in options[u]:
                mask = 0
                for index, pv in enumerate(options[v]):
                    if all(not (((v in pu) == (w in pu)) and
                                ((u in pv) == (w in pv))) for w in common):
                        mask |= 1 << index
                masks.append(mask)
            allowed[u, v] = masks

    cycles = set()
    for a, b, c, d in permutations(range(n), 4):
        if b in h[a] and c in h[b] and d in h[c] and a in h[d]:
            seq = (a, b, c, d)
            reps = [seq[i:] + seq[:i] for i in range(4)]
            rev = seq[::-1]
            reps += [rev[i:] + rev[:i] for i in range(4)]
            cycles.add(min(reps))
    clauses = []
    for cyc in sorted(cycles):
        masks = []
        for index, u in enumerate(cyc):
            prev, nex = cyc[index - 1], cyc[(index + 1) % 4]
            masks.append(sum(1 << k for k, p in enumerate(options[u])
                             if (prev in p) != (nex in p)))
        clauses.append((cyc, masks))
    return j, h, options, allowed, clauses


def solve(h, options, allowed, clauses):
    stats = {"nodes": 0, "dead_ends": 0, "domain_deletions": 0}

    def propagate(domains):
        changed = True
        while changed:
            changed = False
            for (u, v), masks in allowed.items():
                new = sum(1 << k for k in range(10)
                          if domains[u] >> k & 1 and masks[k] & domains[v])
                if not new:
                    return False
                if new != domains[u]:
                    stats["domain_deletions"] += (domains[u] ^ new).bit_count()
                    domains[u] = new
                    changed = True
            for cycle, masks in clauses:
                # The four-cycle is harmless if some vertex must switch ports.
                if any(domains[u] & ~mask == 0 for u, mask in zip(cycle, masks)):
                    continue
                possible = [(u, mask) for u, mask in zip(cycle, masks)
                            if domains[u] & mask]
                if not possible:
                    return False
                if len(possible) == 1:
                    u, mask = possible[0]
                    new = domains[u] & mask
                    if new != domains[u]:
                        stats["domain_deletions"] += (domains[u] ^ new).bit_count()
                        domains[u] = new
                        changed = True
        return True

    def search(domains):
        stats["nodes"] += 1
        if not propagate(domains):
            stats["dead_ends"] += 1
            return None
        candidates = [(d.bit_count(), u) for u, d in enumerate(domains)
                      if d.bit_count() > 1]
        if not candidates:
            return [d.bit_length() - 1 for d in domains]
        _, u = min(candidates)
        for k in range(10):
            if domains[u] >> k & 1:
                child = domains.copy()
                child[u] = 1 << k
                answer = search(child)
                if answer is not None:
                    return answer
        return None

    answer = search([(1 << 10) - 1] * 11)
    return answer, stats


def verify(j, h, options, chosen):
    edges = [(2 * u, 2 * u + 1) for u in range(11)]
    for u in range(11):
        for v in h[u]:
            if u < v:
                pu = int(v not in options[u][chosen[u]])
                pv = int(u not in options[v][chosen[v]])
                edges.append((2 * u + pu, 2 * v + pv))
    adj = [set() for _ in range(22)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert len(edges) == 44
    assert all(len(a) == 4 for a in adj)
    triangles = [tri for tri in combinations(range(22), 3)
                 if all(v in adj[u] for u, v in combinations(tri, 2))]
    square_opposite_pairs = [(u, v) for u, v in combinations(range(22), 2)
                             if len(adj[u] & adj[v]) >= 2]
    assert not triangles and not square_opposite_pairs
    match = edges[:11]
    for u, v in combinations(range(11), 2):
        clash = any(y in adj[x] for x in match[u] for y in match[v])
        assert clash == (v in h[u])
    return edges


def main():
    j, h, options, allowed, clauses = build()
    assert all(len(x) == 4 for x in j)
    assert all(len(x) == 6 for x in h)
    assert all(not (j[u] & j[v]) for u in range(11) for v in j[u])
    assert sum(all(v not in j[u] for u, v in combinations(q, 2))
               for q in combinations(range(11), 5)) == 0
    result, stats = solve(h, options, allowed, clauses)
    data = {"found_girth_five_port_realization": result is not None,
            "H_edges": [(u, v) for u in range(11) for v in h[u] if u < v],
            "domain_sizes": [len(x) for x in options],
            "triangle_binary_constraints": len(allowed),
            "four_cycle_constraints": len(clauses),
            "search_statistics": stats}
    if result is not None:
        data["chosen_port_zero"] = [sorted(options[u][result[u]]) for u in range(11)]
        data["G_edges"] = verify(j, h, options, result)
        data["matching"] = data["G_edges"][:11]
    Path("research/matching_six_obstacle_result.json").write_text(
        json.dumps(data, indent=2), encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
