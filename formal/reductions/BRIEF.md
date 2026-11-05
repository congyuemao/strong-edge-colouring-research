# Formalize Part II and the older structural results of the manuscript

New Lean project in this directory. Read `reference\MANUSCRIPT_zh.md` sections 2, 4, 5 and 6, `reference\ROUTE_Q_zh.md`, `reference\RESULTS.md`. `reference\Definitions.insertion.lean` shows the definitions used by the sister project (`L2 G` on `G.edgeSet`, `MaxDegreeFour`); reuse the same form, but this project is self-contained: do not edit other projects. Mathlib is local (see `lakefile.toml`); never fetch anything; never install anything on drive C. Use `build.ps1` with your module list. Be adversarial: lead `REPORT.md` with any flaw found in a paper statement or proof. No `sorry`, no new axioms, no `native_decide`. Never weaken a statement silently. Cited theorems (Brooks, the Lovasz partition argument if not in Mathlib, Cameron) are explicit hypotheses named by a `def ... : Prop`, unless you can prove them.

Targets, in order:
1. Section 4.1: Lemmas 4.1-4.4, 4.6, 4.6', 4.8; Lemma 4.5 (prove it from chordality if you can: the sister project's `E:\lean\se20-insertion\Se20Insertion\ForestL2.lean`, `ChordalFan.lean` may be copied here, so that the Cameron citation goes away); Lemma 4.7; Theorem 4.9.
2. Section 4.2: Lemma 4.10, Theorem 4.11, Lemma 4.12.
3. Section 5: items 5.6, 5.7 where the statement does not need a large finite certificate.
4. Section 6 and `RESULTS.md`: R13 (at most 41 edges implies 20 colours; a 21-critical edge set has at least 42 edges), the reducibility statements with a paper proof, and the auxiliary theorems of 6.3.
5. Section 1 of `reference\NEW_DIRECTIONS_zh.md`: Proposition 1.1 with the cited Kostochka statement as a hypothesis; the local-injection pull-back corollary at line 215.

When one item resists for a long time, record exactly what blocks it and go on. Write `AxiomAudit.lean` with `#print axioms` for all main results, and `REPORT.md`: flaws first, exact statements, files, axiom output, what is not done.
