# Fifth pass: everything still unformalized in section 11

Read `REPORT.md`–`REPORT4.md` and `reference\NEW_DIRECTIONS_zh.md`. Be adversarial: lead the report with any flaw found in a paper statement or proof. No `sorry`, no new axioms, no `native_decide`, no change to existing theorem statements. Build with `build.ps1`, extend `AxiomAudit.lean`. Work through the list in order; when one item resists for a long time, record exactly what blocks it and go on. Never weaken a statement silently: if a paper statement is false or needs a further hypothesis, say so first and prove the corrected form.

Targets (numbering as in `reference\NEW_DIRECTIONS_zh.md`):
1. Corollary 11.19, Lemma 11.20, Lemma 11.21, Lemma 11.22, Corollary 11.23, Lemma 11.24 and its tree-like corollary, Corollary 11.25.
2. Lemma 11.28 (which swaps unblock h) and the single-edge recolouring gain formula in 11.20.
3. Theorem 11.39, Corollary 11.40, Proposition 11.41. For 11.40 item 4 and Corollary 11.34, take Proposition 11.33 as an explicit hypothesis, as `theorem_F_of_D` does in the fractional project.
4. Lemma 11.1, Lemma 11.2 (covering), Lemma 11.4, Proposition 11.5, Corollary 11.8 (the chain part), Lemma 11.10, the pull-back corollary at line 215 of the document.
5. Proposition 11.49 and the core theorem for an arbitrary number of colours K and the ratio (2K - d)/d from section 11.27. If `Colour` being `Fin 20` makes a general K too invasive, add a new parametrized development in a new module rather than altering existing statements, and show that K = 20 recovers the existing statement.

Write `REPORT5.md`: flaws first, then exact statements, files, the `#print axioms` output for the additions, and what is not done.
