"""Decode one SAT witness of exp9 (typed potential, spread triangle) and print e0's closures."""
import sys
import exp9_potentials as X
from exp8_local_sat import pair_types
name = sys.argv[1] if len(sys.argv) > 1 else "S(u),T(a other)"
opts = set((sys.argv[2] if len(sys.argv) > 2 else "typed,R5").split(","))
f, g = pair_types()[name]
M = X.build(6, 10, f, g, opts)
assert M.s.solve()
mod = set(l for l in M.s.get_model() if l > 0)
cls = {e: next(c for c in range(10) if M.x[e, c] in mod) for e in M.E}
deg = lambda e, c: sum(1 for n in M.nbrs(e) if cls[n] == c)
for e in ((0, 1), f, g):
    print(f"cycle edge {e}: class-degree vector {[deg(e, c) for c in range(10)]}")
    for j in range(1, 10):
        xs = [n for n in M.nbrs(e) if cls[n] == j]
        if len(xs) == 2:
            x, y = xs
            hub = [h for h in xs if set(h) & set(e)]
            print(f"   class {j}: closure {x},{y}  K2={y in X.nbset(M, x)}  span={X.span(e, x, y)}  hub={hub}")
