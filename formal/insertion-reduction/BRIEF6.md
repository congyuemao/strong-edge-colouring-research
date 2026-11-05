# Sixth pass: the targets REPORT5 left open

Read `REPORT5.md` ("What is not done, and the precise blockers") and `reference\NEW_DIRECTIONS_zh.md`. `reference\MANUSCRIPT_zh.md` section 7 is the organized statement of the same results and has corrected proofs of 11.22 and 11.20's triangle example: use it. Same rules: no `sorry`, no new axioms, no `native_decide`, no change to existing statements, nothing weakened silently, flaws first in the report.

There is time: do not stop at a partial result while a target can still be attacked. Work in this order, and when one blocks, record the exact obstruction and go on.

1. 11.22 items 2 and 3 and the full operational statement. The direct proof in the manuscript needs no tree-like hypothesis: count the at most 19 coloured conflicts of `ux_i`.
2. 11.25 item 2, including the overlap cases in the ambient graph.
3. The tree-like corollary of 11.24.
4. 11.41 items 2, 3, 4.
5. The single-edge recolouring gain formula with `b != p`: build the exact component-count deletion/insertion identity.
6. 11.4, 11.5. For the 66-pair bound, a kernel-checked finite statement about the exact 24-vertex conflict pattern is acceptable if `decide` or a structured proof can do it without `native_decide`.
7. 11.1 on an infinite 4-regular tree: decide whether a partial colouring with finite domain is enough to state it, and say what you did.
8. 11.40 item 5: prove Gallai's theorem for vertex-critical graphs, or the form actually needed, if feasible.
9. Also from section 7 of the manuscript: the proposition P2 identity (14D + 3B = 2n + 10M + 3T + 7E + 6Z + L) in section 7.5 and the Delta-beta formula for a hole move in section 7.6.

Write `REPORT6.md`: flaws first, exact statements, files, `#print axioms` output for the additions, what is not done. Extend `AxiomAudit.lean` and `build.ps1`.
