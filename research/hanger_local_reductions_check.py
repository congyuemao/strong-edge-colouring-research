"""Independent finite truth tables for the private-triangle reductions.

This checks local extension equivalences only. The global critical-graph
argument is a separate mathematical proof, not inferred from these tables.
"""
from itertools import product
from pathlib import Path
import json


def proper(values, edges):
    return all(values[u] != values[v] for u, v in edges)


short_path = []
for cq, cu, cv in product(range(3), repeat=3):
    choices = []
    for cs, ct in product(range(3), repeat=2):
        col = [cq, cu, cv, cs, ct]
        if proper(col, [(0, 3), (0, 4), (3, 4), (1, 3), (2, 4)]):
            choices.append([cs, ct])
    # Boundary vertices with different colors always allow extension.
    assert cu == cv or choices
    # The exact relation is also recorded for independent inspection.
    assert bool(choices) == (cu != cv or cu == cq)
    short_path.append({"q_u_v": [cq, cu, cv], "extensions": choices})


five_cycle = []
for cq, cr, cx in product(range(3), repeat=3):
    cycle_choices = []
    triangle_choices = []
    for low in product(range(3), repeat=5):
        # Cycle s-t-u-v-w-s; q sees s,t; r sees u,v; x sees w.
        if (all(low[i] != low[(i + 1) % 5] for i in range(5))
                and low[0] != cq and low[1] != cq
                and low[2] != cr and low[3] != cr and low[4] != cx):
            cycle_choices.append(list(low))
    for low in product(range(3), repeat=3):
        if len(set(low)) == 3 and all(a != b for a, b in zip(low, [cq, cr, cx])):
            triangle_choices.append(list(low))
    expected = len({cq, cr, cx}) > 1
    assert bool(cycle_choices) == expected
    assert bool(triangle_choices) == expected
    five_cycle.append({"q_r_x": [cq, cr, cx],
                       "five_cycle_extensions": cycle_choices,
                       "triangle_extensions": triangle_choices})

out = {"scope": "Finite local extension identities, not a global coloring certificate",
       "path_boundary_assignments": len(short_path),
       "five_cycle_boundary_assignments": len(five_cycle),
       "all_identities_verified": True,
       "path_table": short_path, "cycle_table": five_cycle}
Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in out.items() if not k.endswith('_table')}))
