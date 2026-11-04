# Lean: the conjectures imply the 20-colour bound

Status of the conditional proof in [NEW_DIRECTIONS 11.14, 11.20 and 11.22](../../docs/NEW_DIRECTIONS_zh.md). The work was done by Codex from [BRIEF.md](BRIEF.md) in `E:\lean\se20-insertion`; its own account is [REPORT.md](REPORT.md), which also has the exact Lean statements of the definitions and conjectures.

## What is proved in Lean

For every finite simple graph with maximum degree at most 4, 20 colours suffice if any one of these holds: `Conj119Star`, `Conj119`, `Conj1115`, `Conj1126Weak`, `StarInsertion`. Also `Conj119 → Conj119Star`. These conjectures remain unproved and appear only as explicit hypotheses.

Proved without a hypothesis: Theorem 11.7 at k = 1, Theorems 11.14 and 11.18, Lemmas 11.6, 11.11, 11.12, 11.13, 11.17, 11.36, 11.37, and the 4-regular completion of Proposition 11.38. The 16 + k count and the numerical part of Corollary 11.8 are also proved.

## Checked independently of Codex (2026-11-05)

- Deleted this project's build output and re-ran `lake build`: 3188 jobs, success.
- Re-ran `Se20Insertion/AxiomAudit.lean`: every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
- Searched the sources for `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `implemented_by`, `extern`: none.
- Read the definitions and the statements of the conjectures and of the main theorems against the documents.
- Re-checked the example in [TRIANGLE_COUNTEREXAMPLE.json](TRIANGLE_COUNTEREXAMPLE.json) with separate code.

The proofs themselves were checked only by the Lean kernel, not read.

## Not done

General chains (k ≥ 2) of Theorem 11.7; the chain part of Corollary 11.8; Lemma 11.16; Lemmas 11.19–11.25; Theorem 11.44.

## Build

Run `build.ps1` or `lake build` with the local Mathlib path in `lakefile.toml`; it needs `leanprover/lean4:v4.35.0-rc4`.
