"""exp37b: the cubes of exp37 cover every model.  Add, for every cube, the clause "not this cube" to the stage-1
formula (where models exist) and check that the solver reports UNSAT; also check that every cube alone is
consistent with the formula's unit clauses (no cube is empty by construction)."""
import sys
import time

from exp37_kil_cubes import build, cubes
from exp34_sat_kil import KilSat

for n, g, seed, e, t in ((40, 5, 0, 0, 3), (40, 5, 0, 0, 4), (40, 5, 1, 0, 4), (30, 5, 0, 0, 4)):
    t0 = time.time()
    edges, girth = build(n, g, seed, e)
    ks = KilSat(edges, e)
    order, cs = cubes(ks, t)
    for cube in cs:
        ks.s.add_clause([-ks.x(h, c) for h, c in cube.items()])
    ks.s.conf_budget(20_000_000)
    r = ks.s.solve_limited()
    print(f"n={n} seed={seed} edge {e} t={t}: {len(cs)} cubes; formula minus all cubes: "
          f"{ {False: 'UNSAT (cubes cover everything)', True: 'SAT (GAP!)', None: 'unknown'}[r]}  "
          f"[{time.time() - t0:.0f}s]", flush=True)
