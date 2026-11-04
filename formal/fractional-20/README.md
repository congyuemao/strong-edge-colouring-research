# Formal and independent checks of chi_f(L^2(G)) <= 20

Status of [Theorem 11.29](../../docs/NEW_DIRECTIONS_zh.md) (Δ(G) ≤ 4 implies χ_f(L²(G)) ≤ 20). The work was done by Codex from
[BRIEF.md](BRIEF.md) and [BRIEF2.md](BRIEF2.md) in `E:\lean\se20-fractional`; its own accounts are [REPORT.md](REPORT.md) and
[REPORT2.md](REPORT2.md).

## What is established, and how

| Statement | Status |
|---|---|
| Lemma C (degree formula, Lemma 11.32) | Lean, unconditional |
| Lemma B (peeling, Lemma 11.31) | Lean, unconditional. Codex found that the first paper proof omitted a normalization step |
| Lemma A (local fractional Reed, Lemma 11.30) | Lean, unconditional, by Reed's process (`local_fractional_reed_elementary`). An older version conditional on LP duality is kept |
| Proposition D (Proposition 11.33) | UNSAT under two independent encodings; LRAT certificate for one of them. In Lean it is only reduced to a finite statement on `Fin 23` ([PropositionDReduction.lean](second_pass/PropositionDReduction.lean)) |
| Theorem F (Theorem 11.29) | `theorem_F_of_D` in Lean, with `PropositionD` as its only hypothesis |

`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every theorem ([axioms.txt](second_pass/axioms.txt)). This
does not cover the hypothesis of `theorem_F_of_D`.

## Checked independently of Codex

Re-run on 2026-11-04: `lake build`, `#print axioms` for both passes, compilation of `PropositionDReduction.lean`, the SHA256 of `d16.cnf`, and
`check_lrat.exe` on the certificate. The source of `encode.cpp` and the Lean statements of the definitions and of `theorem_F_of_D` were read, and the Lean sources were searched for `sorry`, `axiom`, `native_decide` and `ofReduceBool`.

Not re-run: the Lean standard-library checker replay ([log](independent/d16.std-check.log)), the solver run, and the positive controls.

## Certificate

Not stored here because of its size; regenerate it with `independent/reproduce_sat.ps1`. A new run may give a different valid proof.

```text
d16.cnf   37,510,408 bytes  SHA256 05F89B4089DDB6668E1FC5DC8873FC807DE1A487BF81A9DE60A8628E0420F8D4
d16.lrat 477,598,828 bytes  SHA256 6E60536ABFA146C11EF7D7F9F7072AB20ADAA4EEDA836F41F0CEF57C994FC3D2
```

## Not established

- No Lean proof of the finite statement on `Fin 23`, so `PropositionD` is not discharged. The missing link is from the graph statement to a concrete CNF: variable numbering, Tseitin and counter clauses, and the symmetry breaking the certificate relies on.
- The standard-library checker was executed as a program. It is not a kernel-checked proof term for this CNF.
- No SAT-free exhaustive enumeration, and no paper proof of Proposition D.
