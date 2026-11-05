# Fourth pass: Lemma 11.48 (the fan lemma) and the bound 87

Part 4 of `BRIEF3.md`, now the main task. Read `REPORT3.md` and section 11.26 of `reference\NEW_DIRECTIONS_zh.md`. Be adversarial: lead the report with any flaw. No `sorry`, no new axioms, no change to existing statements.

1. `L2 T` is chordal for a tree `T` (or forest): every cycle of length at least 4 in `L2 T` has a chord. Choose whatever form is easiest, for instance "every induced cycle in `L2 T` is a triangle", or via a perfect elimination order from a leaf.
2. Lemma 11.48 in `G`: let `φ` be a partial colouring of `L2 G`, `v` not coloured `a, b`, and `P` a shortest path in the `(a, b)` Kempe graph from an `a`-neighbour to a `b`-neighbour of `v`. Let `E'` be the edges of `P`, the edge `v`, and for each consecutive pair of the cycle `v, P, v` an edge of `G` realizing the conflict when they share no endpoint. If `G` restricted to the vertices of `E'` is a forest (no cycle in the induced graph), then every vertex of `P` is adjacent to `v` in `L2 G`, and in particular `v` has an `a`-neighbour and a `b`-neighbour conflicting with each other. State the hypothesis so that it is as weak as the proof allows, and say if the statement in the document is wrong.
3. Consequence: if `(a, b)` is tangled at `v` with no conflicting `a`- and `b`-neighbours, then `P` together with `v` spans a cycle of `G`; if `G` has girth at least `g`, then `|P| ≥ g/2 - 1`.
4. For `G` of maximum degree at most 4 and girth at least 7: `|E(L2[N(v)])| ≤ 87`. A short proof: `n = |N(v)| ≤ 24`, `t ≤ 6` neighbours share an endpoint with `v`, and `GirthGeometry.common_near_card`, `common_far_card` bound the degrees in `L2[N(v)]` by 14 and 5. Then the number of pairs tangled at `v` in direct form is at most 87.

Write `REPORT4.md` with exact statements, files, `#print axioms` output (extend `AxiomAudit.lean`), and what is not done. Stop when all build, or report exactly what blocks them.
