# Seventh pass: the last items of section 11

Read `REPORT6.md` ("What is not done"). Same rules: no `sorry`, no new axioms, no `native_decide`, no change to existing statements, nothing weakened silently, flaws first.

1. Gallai's theorem in the form needed for Corollary 11.40 item 5: a finite connected graph with an uncolourable list assignment whose lists have size at least the degree of the vertex has every block a clique or an odd cycle (the Borodin / Erdos-Rubin-Taylor degree-choosability theorem). `critical_low_degree_list_obstruction` already supplies the lists. Prove it and finish 11.40(5). Mathlib has block-free tools only, so choose the most economical formulation, for instance by induction with a non-separating pair argument, and say what you used.
2. The geometric labelling for 11.5: construct the map to the verified 24-vertex pattern from a tree-like (girth at least 7, or `locallyTreeAt`) neighbourhood of a hole, so that `sixty_six_chains` becomes a statement with no map hypothesis.
3. The P4 statement (saturation propagates two steps) and P7 (class-size square potential) of `reference\MANUSCRIPT_zh.md` section 7.5, and the equivalent form of Conjecture 11.9 in section 7.3, which is an actual theorem (each one-step-stuck state has a non-one-step-stuck neighbour iff 11.9).
4. Anything else in `reference\MANUSCRIPT_zh.md` sections 7 and 8.2 tagged 【证明】 with no Lean name, by your own scan of that text. List what you found first; then prove as many as you can.

Write `REPORT7.md`: flaws first, exact statements, axiom output, what is not done. Extend `AxiomAudit.lean` and `build.ps1`.
