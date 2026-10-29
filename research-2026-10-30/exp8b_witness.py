"""Decode one SAT witness of exp8 (K=10, R=7, R5) and describe e0's stuck pattern."""
import sys
from exp8_local_sat import build, pair_types
from sec import norm
name = sys.argv[1] if len(sys.argv) > 1 else "S(u),S(u)"
f, g = pair_types()[name]
M = build(7, 10, f, g, True)
assert M.s.solve()
mod = set(l for l in M.s.get_model() if l > 0)
cls = {e: next(c for c in range(10) if M.x[e, c] in mod) for e in M.E}
def deg(e, c): return sum(1 for n in M.nbrs(e) if cls[n] == c)
e0 = (0, 1)
print("pattern:", name)
print("e0 class-degree vector:", [deg(e0, c) for c in range(10)])
for j in range(1, 10):
    xs = [n for n in M.nbrs(e0) if cls[n] == j]
    if len(xs) == 2:
        x, y = xs
        adj = y in M.nbrs(x)
        print(f" class {j}: x={x} y={y} conflict(x,y)={adj}  d_j(x)={deg(x,j)} d_j(y)={deg(y,j)}  x-vector={[deg(x,c) for c in range(10)]}")
