"""Targeted local search for the balanced A-four-neighbour stopping pattern.

Only fresh external ports are used: negative results do not cover all possible
identifications or edges between external vertices.  No global optimality is
claimed for positive results.
"""
from itertools import combinations
import json
from pathlib import Path
from small_clique_insertion_obstruction import edge, adj, conflicts, girth_at_least_five


def fresh_completion(n, core, chosen_red):
    red = set(chosen_red)
    blue = set(core) - red
    nv = n
    def append_leaf(v, dest):
        nonlocal nv
        dest.add(edge(v, nv))
        nv += 1
    for v in range(n):
        for _ in range(2 - sum(v in e for e in red)):
            append_leaf(v, red)
    for v in range(n):
        for _ in range(2 - sum(v in e for e in blue)):
            append_leaf(v, blue)
    first_layer = set(range(nv))
    for v in sorted(first_layer - set(range(n))):
        for _ in range(2 - sum(v in e for e in red)):
            append_leaf(v, red)
    ng = adj(nv, sorted(red | blue))
    girth_at_least_five(ng)
    assert all(len(ng[v]) == 4 for v in range(n))
    assert max(map(len, ng)) <= 4
    assert all(sum(v in e for e in red) == 2 for v in first_layer)
    assert max(map(len, adj(nv, sorted(blue)))) <= 2
    return nv, sorted(red | blue), sorted(red)


def solve(h, nqs, root, triple):
    boundary = set(range(5, len(h)))
    roots = [h[i] & boundary for i in range(5)]
    assert all(len(s) == 8 for s in roots)
    # 0=B and 1=C; the central q belongs to B in the current partition.
    assigned = {v: (0 if v in triple else 1) for v in roots[root]}
    extra_b = {v: int(v in roots[root]) for v in boundary}
    wanted = [3 if i == root else 4 for i in range(5)]
    nodes = 0

    def search(col):
        nonlocal nodes
        nodes += 1
        col = dict(col)
        while True:
            forced = {}
            def force(v, value):
                if v in col:
                    return col[v] == value
                if v in forced:
                    return forced[v] == value
                forced[v] = value
                return True
            for i, ns in enumerate(roots):
                used = sum(col.get(v) == 0 for v in ns)
                free = ns - col.keys()
                if used > wanted[i] or used + len(free) < wanted[i]:
                    return None
                if used == wanted[i]:
                    for v in free:
                        if not force(v, 1):
                            return None
                if used + len(free) == wanted[i]:
                    for v in free:
                        if not force(v, 0):
                            return None
            for v, c in col.items():
                ns = h[v] & boundary
                same = sum(col.get(u) == c for u in ns)
                limit = 3 - (extra_b[v] if c == 0 else 0)
                if same > limit:
                    return None
                if same == limit:
                    for u in ns - col.keys():
                        if not force(u, 1-c):
                            return None
            if not forced:
                break
            col.update(forced)
        if len(col) == len(boundary):
            # Necessary single-move test. Unseen conflict neighbours may be
            # distributed among parts, but each eventual vertex has degree 12.
            # A positive result remains only a locally extendible degree table.
            part_sets = [set(range(5)) - {root},
                         {root} | {v for v, c in col.items() if c == 0},
                         {v for v, c in col.items() if c == 1}]
            for v in range(len(h)):
                part = next(j for j in range(3) if v in part_sets[j])
                low = [len(h[v] & ss) for ss in part_sets]
                possible = False
                for a in range(low[0], 13):
                    for b in range(low[1], 13-a):
                        c = 12-a-b
                        ds, rs = [a, b, c], [4, 3, 3]
                        if c >= low[2] and ds[part] <= rs[part] and all(
                                ds[j]-ds[part]+rs[part]-rs[j] >= 0 for j in range(3)):
                            possible = True
                if not possible:
                    return None
            return col
        v = max(boundary - col.keys(), key=lambda v:
                (sum(u in col for u in h[v] & boundary),
                 sum(v in rs for rs in roots), len(h[v] & boundary), -v))
        for c in (0, 1):
            col[v] = c
            result = search(col)
            if result is not None:
                return result
        return None

    result = search(assigned)
    if result is not None:
        assert all(sum(result[v] == 0 for v in ns) == wanted[i]
                   for i, ns in enumerate(roots))
        for v, c in result.items():
            assert sum(result.get(u) == c for u in h[v] & boundary) + \
                   (extra_b[v] if c == 0 else 0) <= 3
    return result, nodes


def main():
    data = json.loads(Path(__file__).with_name("factor_five_clique_geometry_check.json").read_text(encoding="utf-8"))
    cases = {key: value for key, value in data["five_edge_forests"].items() if value["count"]}
    cases["C5"] = {"vertices": 5, "Q": [(i, (i+1)%5) for i in range(5)],
                   "example_edges": [(i, (i+1)%5) for i in range(5)]}
    output = {}
    for shape, data in cases.items():
        n = data["vertices"]
        qq = [edge(*e) for e in data["Q"]]
        core = set(edge(*e) for e in data["example_edges"])
        optional = sorted(core - set(qq))
        counts = {"admissible_core_F_choices": 0, "triple_cases": 0,
                  "search_nodes": 0, "positive_roots": []}
        for mask in range(1 << len(optional)):
            rr = set(qq) | {e for i, e in enumerate(optional) if mask >> i & 1}
            if max(map(len, adj(n, sorted(rr)))) > 2 or \
                    max(map(len, adj(n, sorted(core-rr)))) > 2:
                continue
            counts["admissible_core_F_choices"] += 1
            nv, edges, red = fresh_completion(n, core, rr)
            selected = qq + [e for e in red if e not in qq]
            hh = conflicts(adj(nv, edges), selected)
            boundary_ids = sorted(set.union(*(hh[i] for i in range(5))) - set(range(5)))
            selected = qq + [selected[i] for i in boundary_ids]
            hh = conflicts(adj(nv, edges), selected)
            for root in range(5):
                if any(s["root"] == root for s in counts["positive_roots"]):
                    continue
                nb = hh[root] - set(range(5))
                for triple in combinations(sorted(nb), 3):
                    if not all(v in hh[u] for u, v in combinations(triple, 2)):
                        continue
                    counts["triple_cases"] += 1
                    answer, nodes = solve(hh, 5, root, set(triple))
                    counts["search_nodes"] += nodes
                    if answer is not None:
                        counts["positive_roots"].append(
                            {"root": root, "core_F_mask": mask, "G_vertices": nv,
                             "G_edges": edges, "F_edges": red,
                             "selected_F_edges": selected,
                             "B_indices": [root] + sorted(v for v, c in answer.items() if c == 0),
                             "C_indices": sorted(v for v, c in answer.items() if c == 1),
                             "A_indices": [i for i in range(5) if i != root],
                             "root_B_K4": [root] + list(triple)})
                        break
        output[shape] = counts
    # A single additional external blue edge matters.  For the five-matching
    # kernel, take q=uv, a another core neighbour of u, and give u,v,a their
    # external red continuations ux,vy,az.  Adding blue yz makes these three
    # continuations the B triangle around q.  This explicitly prevents the
    # fresh-port negative result from being mistaken for a general theorem.
    data = cases["1,1,1,1,1"]
    n = data["vertices"]
    qq = [edge(*e) for e in data["Q"]]
    core = set(edge(*e) for e in data["example_edges"])
    nv, edges, red = fresh_completion(n, core, set(qq))
    nc = adj(n, sorted(core))
    records = []
    trials, positives = 0, 0
    for root, (u, v) in enumerate(qq):
        for x, y in ((u, v), (v, u)):
            ex = next(e for e in red if x in e and e not in qq)
            ey = next(e for e in red if y in e and e not in qq)
            for a in sorted(nc[x] - {y}):
                ea = next(e for e in red if a in e and e not in qq)
                py = next(t for t in ey if t != y)
                pa = next(t for t in ea if t != a)
                augmented = edges + [edge(py, pa)]
                ng = adj(nv, augmented)
                girth_at_least_five(ng)
                assert max(map(len, ng)) <= 4
                assert max(map(len, adj(nv, sorted(set(augmented)-set(red))))) <= 2
                selected = qq + [e for e in red if e not in qq]
                hh = conflicts(ng, selected)
                triple = {selected.index(e) for e in (ex, ey, ea)}
                assert all(j in hh[i] for i, j in combinations(triple, 2))
                answer, nodes = solve(hh, 5, root, triple)
                trials += 1
                if answer is not None:
                    positives += 1
                    if not any(s["root"] == root for s in records):
                        records.append({"root": root, "extra_blue_edge": edge(py, pa),
                                        "G_vertices": nv, "G_edges": augmented,
                                        "F_edges": red, "selected_F_edges": selected,
                                        "B_indices": [root] + sorted(v for v, c in answer.items() if c == 0),
                                        "C_indices": sorted(v for v, c in answer.items() if c == 1),
                                        "A_indices": [i for i in range(5) if i != root],
                                        "root_B_K4": [root] + sorted(triple)})
    output["matching_one_cross_edge"] = {"tested_cases": trials, "positive_cases": positives,
                                         "positive_roots": records}
    output["scope"] = "Local models only: fresh ports and the explicitly listed one-cross-edge matching models. Positive cases satisfy local part degree bounds and each partial degree table admits a 12-degree completion with no negative single move; this does not assert a simultaneous graph completion or global minimality."
    output["search_versions"] = json.loads(Path(__file__).with_name(
        "small_clique_balanced_gate_search_history.json").read_text(encoding="utf-8"))
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    print(json.dumps({k: {a: b for a, b in v.items() if a != "positive_roots"} |
                        {"positive_root_ids": [s["root"] for s in v["positive_roots"]]}
                      for k, v in output.items() if isinstance(v, dict)}, indent=2))


if __name__ == "__main__":
    main()
