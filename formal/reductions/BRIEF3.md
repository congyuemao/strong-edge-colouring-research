# Third pass: the rest of Part II and of the older results

Read `REPORT.md` (Second pass, remaining obstructions). Same rules: no `sorry`, no new axioms, no `native_decide`, no change to proved statements, nothing weakened silently, cited theorems only as named hypotheses, flaws first. There is time: do not stop at a partial result while a target can still be attacked.

Order:
1. Lemma 4.7 and Theorem 4.9.
2. G05 (at most 41 edges implies 20 colours; a 21-critical edge set has at least 42 edges), with the independence-number-two colouring assertion; finite checks only if kernel-checkable without `native_decide`, otherwise each as a separately named hypothesis, and report their exact size.
3. G12, then G13, G14, G16 (with G15 as a named hypothesis), G02, G07's reduction.
4. A03, A04, A02, A06.
5. F03, F04, F05, F07, the rest of F09; then the S group (S02, S06, S07, S08, S17, S19, S20).

Append a section "Third pass" to `REPORT.md`, and update `AxiomAudit.lean`, `build.ps1`.
