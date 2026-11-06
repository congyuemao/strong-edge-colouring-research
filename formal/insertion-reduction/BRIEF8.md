# Eighth pass: Gallai, P6, the count corollaries

Read `REPORT7.md`. Same rules: no `sorry`, no new axioms, no `native_decide`, no change to existing statements, nothing weakened silently, flaws first. Memory on this machine is tight: at most one `lean` process at a time, `-j1`. Retry only on `failed to read file`.

1. Finish Gallai's degree-choosability theorem (the Borodin / Erdos-Rubin-Taylor classification: a connected graph with an uncolourable list assignment with |L(v)| >= deg(v) is a Gallai tree), then Corollary 11.40(5). You have `colourable_of_one_slack`, `colourable_of_list_difference`, `colourable_of_nonseparating_pair`. What is missing is the structural step: a 2-connected graph that is neither complete nor an odd cycle has two nonadjacent vertices with a common neighbour whose deletion leaves it connected, or the classical proof via an induced even cycle with at most one chord (Rubin's block lemma), whichever is shorter; then the reduction to blocks. Prove what you need about blocks directly for finite graphs; do not build general block-graph theory if a leaf-block induction is enough.
2. P6 (section 7.7 of `reference\MANUSCRIPT_zh.md`): the C/L/U family, an abstract construction with the stated degrees, and the core computation.
3. The numerical corollaries: L(h) >= 103, mean L(f) >= 27, L(f_p) >= 84, stated at girth at least 7.

Write `REPORT8.md`: flaws first, exact statements, axiom output, what is not done. Extend `AxiomAudit.lean` and `build.ps1`.
