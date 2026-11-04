# Audit of exp49_frac_core.py

Read only after the independent full 23-vertex UNSAT certificate passed.
The original file was read, not modified or executed.

No unsound restriction was found for the default m=16, dmin=20, dz=None run,
provided BOTH `tri` and `notri` cases are checked with default nT=m-1.

* A and B are slots for possible neighbours, not an assertion that endpoint
  degrees equal four. Except for the specified common neighbour in the triangle
  case, these edges are optional. Lower endpoint degrees are therefore covered.
* In the triangle case the shared slot 4 is forced adjacent to both endpoints.
  The local bound excludes two common neighbours; the two cases cover all
  possibilities. Non-triangle slots can be filled by isolates.
* The bound is 8+15=23 slots in the non-triangle case, 7+15=22 in the triangle
  case. Empty neighbour slots do not consume the exterior slots: actual
  neighbours occupy their designated slots, and each other selected edge
  contributes at most one actual exterior endpoint. This remains sound even
  when the actual closed neighbourhood has fewer than 7 or 8 vertices.
* Q variables are used only on pairs touching the padded W. Actual clique
  members necessarily touch the actual W and hence this padded W. Pairwise
  conflict with the fixed selected edge enforces the needed real adjacency.
  At least 16 instead of exactly 16 is harmless: an actual counterexample can
  select exactly 16, and a larger model could be reduced to 16.
* `In` encodes the correct disjunction in both directions. `Tri`, `AnyTri`,
  and `Eprime` only have forward implications. This is sufficient: all true
  graph contributions are forced to be counted, and choosing the auxiliaries
  to equal their graph meanings extends every valid graph to a model. No false
  UNSAT is caused by omitting the reverse implications.
* For bound 4, the clauses express t<=1, e'<=4, and (t=1 implies e'=0), exactly
  the intended inequality. Guarding all sequential-counter clauses is safe.
* Double-lex symmetry is sound here. Permutations of T, of A-only slots, and
  of B-only slots preserve every non-symmetry constraint. A row-major
  lexicographically largest matrix in such a finite orbit has its rows sorted
  and its columns sorted within each allowed group. Otherwise an allowed row
  or column swap would increase that same matrix. The shared triangle column
  is excluded from the column groups. The equality-prefix auxiliaries are
  only forced when needed, which is sufficient and admits the exact prefix
  equality assignment.

## Limitations and misleading generality

* `nt=<smaller>` restricts the search; UNSAT from an arbitrary smaller nt is
  not a proof of the full proposition.
* Running only one of tri/notri is not a full check.
* The unconditional t<=1 restriction would be wrong for a generalized local
  bound >=8, and the root layout has no case for two common neighbours. Thus
  `dmin`/`dz` are not sound arbitrary-bound generalizations. This does not affect
  the requested bounds 4 and 5.
* The model checker validates 4t+e'<=24-dmin, not actual L2 degree>=dmin. Those
  properties are not equivalent when degrees are below four. The stronger
  UNSAT reduction only needs the necessary inequality, so its use is sound.
* `check()` does not separately recheck a special `dz` bound. The default
  run does not use dz.
* This file, by itself, emits no proof certificate and therefore cannot supply
  the requested independently checked UNSAT evidence. The evidence in this
  repository comes from the separate implementation.
