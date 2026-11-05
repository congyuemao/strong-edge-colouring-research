# Second pass: Part II and the older structural results

Read `REPORT.md` ("Precise outstanding work"). The missing proof files are now here: `reference\research\` (the old `research/` directory, read only) and `reference\MANUSCRIPT_zh.md`, whose Appendix C has the proofs of the older results copied from those files with their source and line numbers, and whose Appendix E lists known wording gaps. Same rules as `BRIEF.md`: no `sorry`, no new axioms, no `native_decide`, nothing weakened silently, cited theorems only as named hypotheses, no change to statements already proved, flaws first in the report.

There is time: do not stop at a partial result while a target can still be attacked. Work in this order, and when one blocks, record the exact obstruction and go on.

1. The path and cycle decomposition of a finite graph of maximum degree two, with parity; Lemma 4.1's classification; a formal Phi_2.
2. Lemma 4.3, Lemma 4.8, Proposition 1.1 of `reference\NEW_DIRECTIONS_zh.md` (now only the residual bipartiteness argument is missing).
3. Lemmas 4.6, 4.6', 4.7, Theorem 4.9.
4. Lemma 4.10 and Theorem 4.11.
5. Section 5: full item 5.6 where it does not need the finite classification 5.5 (and state 5.5 as an explicit hypothesis where it does).
6. Appendix C, in this order: G06, G08, G09, G12, G05 (the chain of steps at most 41 edges; finite checks only if kernel-checkable without `native_decide`, otherwise a named hypothesis for each), A03, A04, A02, A06, G13, G14, G16 (with G15 as a named hypothesis), F01, F03, F09, then the S group as far as time allows.

Append a section "Second pass" to `REPORT.md`, and update `AxiomAudit.lean` and `build.ps1`.
