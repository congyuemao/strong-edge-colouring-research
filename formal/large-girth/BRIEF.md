# Formalize Part I of the manuscript: large girth

New Lean project in this directory. Read `reference\MANUSCRIPT_zh.md` sections 2 and 3 and `reference\LARGE_GIRTH_zh.md`. `reference\Definitions.insertion.lean` shows the definitions used by the sister project (`L2 G` on `G.edgeSet`, `MaxDegreeFour`); reuse the same form, but this project is self-contained: do not edit other projects. Mathlib is local (see `lakefile.toml`); never fetch anything; never install anything on drive C. Use `build.ps1` with your module list. Be adversarial: lead `REPORT.md` with any flaw found in a paper statement or proof. No `sorry`, no new axioms, no `native_decide`. Never weaken a statement silently.

Cited theorems (Kostochka 1978, Haxell 2001, the Lovasz local lemma) are NOT axioms: state each as a named `def ... : Prop` and take it as an explicit hypothesis of the theorems that need it. Prove the implication from the general Kostochka statement to the special cases (K6) and (K5), including the numerical inequalities with e. If time remains at the end, try to prove the local lemma itself (variable or general asymmetric form) so it stops being a hypothesis.

Targets, in order:
1. Lemma 3.1 (matching contraction, both parts), Lemma 3.2 (assembly), Remark 3.3 (the construction).
2. Theorem 3.4 (Theorem A).
3. Fact 3 of section 2 (ball sizes), steps 1-3 of Theorem 3.5, Lemma 3.6, steps 4-6: Theorem 3.5 (Theorem B). The graph is finite; step 1 needs an Euler orientation and Konig; prove them or find them in Mathlib.
4. Theorems 3.7, 3.8; Lemma 3.9 (a), (b), Corollary 3.10; Lemma 3.11 (tree lemma; decide how to represent the infinite tree, and state what you chose).
5. Proposition 3.13; the Haxell transversal remark after it; Lemma 3.15.
6. Theorem 3.14 (Theorem B+). The numerical step (the transfer matrix M(t), the bound at g = 5710) must be kernel-checked with rational arithmetic if at all feasible, without `native_decide`; if it is not, take the exact numerical inequality as a clearly named hypothesis and say so.

When one item resists for a long time, record exactly what blocks it and go on. Write `AxiomAudit.lean` with `#print axioms` for all main results, and `REPORT.md`: flaws first, exact statements, files, axiom output, what is not done.
