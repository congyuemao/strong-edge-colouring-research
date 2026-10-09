"""Find and verify a two-Kempe repair of the one-step-stable certificate."""
from itertools import combinations
import json
from pathlib import Path
from degree3_verify_certificate import load_and_conflicts, pair_components, extension


def search(data, conflict):
    original, roots = data["colors"], data["root_edges"]
    boundary = set().union(*(conflict[e] for e in roots)) - set(roots)
    palette = set(range(1, 21))
    # First try to cut a synchronized 19/t or 20/t component by recoloring
    # one exterior vertex of the conflict graph to a currently free color.
    pairs = [(t, a) for a in (19, 20) for t in range(10, 19)]
    pairs += list(combinations(range(1, 19), 2))
    trials = 0
    for pair in pairs:
        parts, mapping = pair_components(original, conflict, pair)
        relevant = {mapping[e] for e in boundary if original[e] in pair}
        for index in sorted(relevant):
            for edge in sorted(parts[index] - boundary, key=lambda e: (len(conflict[e]), e)):
                free = palette - {original[f] for f in conflict[edge]} - set(pair)
                if not free:
                    continue
                trials += 1
                recolored = original.copy()
                old, new = original[edge], min(free)
                recolored[edge] = new
                assert extension(recolored, conflict, roots) is None
                new_parts, new_mapping = pair_components(recolored, conflict, pair)
                relevant_new = {new_mapping[e] for e in boundary if recolored[e] in pair}
                for part_id in sorted(relevant_new):
                    component = new_parts[part_id]
                    candidate = recolored.copy()
                    for e in component:
                        candidate[e] = sum(pair) - candidate[e]
                    triple = extension(candidate, conflict, roots)
                    if triple is None:
                        continue
                    for e, color in zip(roots, triple):
                        candidate[e] = color
                    assert all(candidate[e] != candidate[f]
                               for e, ns in enumerate(conflict) for f in ns)
                    return {"first": {"pair": [old, new], "component": [edge]},
                            "second": {"pair": list(pair), "component": sorted(component)},
                            "root_colors": list(triple), "complete_colors": candidate,
                            "trials": trials}
    return None


if __name__ == "__main__":
    source = Path(__file__).with_name("degree3_kempe_stable.json")
    data, adjacency, conflict = load_and_conflicts(source)
    result = search(data, conflict)
    if result is None:
        print("No two-step repair found by the exterior-singleton search.")
    else:
        output = source.with_name("degree3_two_swaps.json")
        output.write_text(json.dumps(result, separators=(",", ":")))
        print("first swap:", result["first"])
        print("first edge endpoints:", data["edges"][result["first"]["component"][0]])
        print("second pair:", result["second"]["pair"])
        print("second component size:", len(result["second"]["component"]))
        print("root colors:", result["root_colors"])
        print("singleton candidates tested:", result["trials"])
        print("complete 20-color repair: independently checked")
        print("certificate:", output.name)
