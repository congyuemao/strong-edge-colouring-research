# Formal and independent checks of chi_f(L^2(G)) <= 20

Status of [Theorem 11.29](../../docs/NEW_DIRECTIONS_zh.md) (Δ(G) ≤ 4 implies χ_f(L²(G)) ≤ 20). The work was done by Codex from
[BRIEF.md](BRIEF.md) in `E:\lean\se20-fractional`; its own account is [REPORT.md](REPORT.md).

## What is established, and how

| Statement | Status |
|---|---|
| Lemma C (degree formula, Lemma 11.32) | Lean, unconditional |
| Lemma B (peeling, Lemma 11.31) | Lean, unconditional. Codex found that the first paper proof omitted a normalization step |
| Lemma A (local fractional Reed, Lemma 11.30) | Lean, conditional on finite LP strong duality (`FractionalDuality`) |
| Proposition D (Proposition 11.33) | Not in Lean. UNSAT under two independent encodings; LRAT certificate for one of them |
| Theorem F (Theorem 11.29) | `theorem_F` in Lean, conditional on `FractionalDuality` and `PropositionD` |

`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every theorem ([axioms.txt](independent/axioms.txt)). This
does not cover the two explicit hypotheses of `theorem_F`.

## Checked independently of Codex

Re-run on 2026-11-04: `lake build`, `lake env lean independent/Axioms.lean`, the SHA256 of `d16.cnf`, and `check_lrat.exe` on the certificate.
The source of `encode.cpp` and the Lean statements in `Definitions.lean` and `TheoremF.lean` were read.

Not re-run: the Lean standard-library checker replay ([log](independent/d16.std-check.log)), the solver run, and the positive controls.

## Certificate

Not stored here because of its size; regenerate it with `independent/reproduce_sat.ps1`. A new run may give a different valid proof.

```text
d16.cnf   37,510,408 bytes  SHA256 05F89B4089DDB6668E1FC5DC8873FC807DE1A487BF81A9DE60A8628E0420F8D4
d16.lrat 477,598,828 bytes  SHA256 6E60536ABFA146C11EF7D7F9F7072AB20ADAA4EEDA836F41F0CEF57C994FC3D2
```

## Not established

- No Lean proof of LP strong duality.
- No Lean proof of the reduction from graphs to the CNF, so `PropositionD` is not discharged.
- The standard-library checker was executed as a program. It is not a kernel-checked proof term for this CNF.
- No SAT-free exhaustive enumeration.
