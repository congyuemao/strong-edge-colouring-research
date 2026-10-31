"""exp36b: in a tree-like N(e) (no short cycles near e), the least number of non-adjacent pairs among 16 singleton
positions.  Each such pair needs a Kempe chain that leaves N[e] and comes back, if e is to be stuck."""
import itertools

from exp32b_occupancy import tree_edge_type

adj = tree_edge_type()
best = min((sum(1 for i, j in itertools.combinations(S, 2) if not (adj[i] >> j) & 1), S)
           for S in itertools.combinations(range(len(adj)), 16))
print(f"positions {len(adj)}; edges of L^2[N(e)] {sum(bin(a).count('1') for a in adj) // 2}; "
      f"least non-adjacent pairs among 16 singletons: {best[0]} (e.g. positions {best[1]})")
