"""Exhaust exact recolorings of the nine vertices of a proposed joint O9.

The boundary is represented only by its three degree counts.  Negative
potential is a rigorous obstruction independent of any boundary completion.
"""
from itertools import combinations, product
from pathlib import Path
import json

# a,b,c,d,u,v,w,z,x, with the two C vertices u,w from distinct odd cycles.
names = "a b c d u v w z x".split()
edges = set(combinations(range(4), 2))
edges |= set(combinations((0, 1, 4, 5), 2))
edges |= set(combinations((2, 3, 6, 7), 2))
edges |= {(4, 8), (5, 8), (6, 8), (7, 8)}
old = (0, 0, 0, 0, 2, 0, 2, 0, 0)
r = (4, 4, 2)
leaf_options = [(4, 5, 3), (3, 4, 5), (3, 5, 4), (3, 6, 3)]
center_options = [(2, 4, 6), (2, 5, 5), (2, 6, 4), (3, 5, 4)]

# Store the common correction once for each proposed recoloring.
moves = []
for new in product(range(3), repeat=9):
    correction = sum(int(new[i] == new[j]) + int(old[i] == old[j])
                     - int(new[i] == old[j]) - int(new[j] == old[i])
                     for i, j in edges)
    moves.append((new, correction))

results = []
for pv, pz, px in product(leaf_options, leaf_options, center_options):
    profiles = [(4, 5, 3)] * 4 + [(5, 5, 2), pv, (5, 5, 2), pz, px]
    costs = [[profile[c] - profile[old[i]] + r[old[i]] - r[c]
              for c in range(3)] for i, profile in enumerate(profiles)]
    best = (0, old)
    cycle_reducing = None
    zero_c_subsets = set()
    for new, correction in moves:
        delta = correction + sum(costs[i][new[i]] for i in range(9))
        if delta < best[0]:
            best = (delta, new)
        if delta == 0:
            cs = tuple(i for i in range(9) if new[i] == 2)
            zero_c_subsets.add(cs)
            if new[4] != 2 and new[6] != 2 and len(cs) <= 1:
                cycle_reducing = {names[i]: "ABC"[new[i]] for i in range(9)}
    results.append({"leaf_v": pv, "leaf_z": pz, "center_x": px,
                    "minimum_delta": best[0],
                    "minimizing_partition": {names[i]: "ABC"[best[1][i]] for i in range(9)},
                    "zero_C_subsets": [[names[i] for i in cs] for cs in sorted(zero_c_subsets)],
                    "cycle_reducing_zero_move": cycle_reducing})

out = {"core_names": names, "core_edges": sorted(edges),
       "initial_partition": {names[i]: "ABC"[old[i]] for i in range(9)},
       "profiles_tested": len(results), "recolorings_each": len(moves),
       "surviving_profiles": [x for x in results if x["minimum_delta"] == 0 and x["cycle_reducing_zero_move"] is None],
       "results": results}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2), encoding="utf-8")
print(json.dumps({"profiles": len(results), "survivors": len(out["surviving_profiles"]),
                  "deltas": sorted(set(x["minimum_delta"] for x in results)),
                  "cycle_reducing_zero_moves": sum(x["cycle_reducing_zero_move"] is not None for x in results),
                  "output": str(path)}, indent=2))
