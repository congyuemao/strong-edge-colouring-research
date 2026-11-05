# Lean: the conjectures imply the 20-colour bound

Status of the conditional proof in [NEW_DIRECTIONS 11.14, 11.20 and 11.22](../../docs/NEW_DIRECTIONS_zh.md). The work was done by Codex from [BRIEF.md](BRIEF.md) in `E:\lean\se20-insertion`; its own account is [REPORT.md](REPORT.md), which also has the exact Lean statements of the definitions and conjectures.

## What is proved in Lean

For every finite simple graph with maximum degree at most 4, 20 colours suffice if any one of these holds: `Conj119Star`, `Conj119`, `Conj1115`, `Conj1126Weak`, `StarInsertion`. Also `Conj119 → Conj119Star`. These conjectures remain unproved and appear only as explicit hypotheses.

Proved without a hypothesis: Theorem 11.7 at k = 1, Theorems 11.14 and 11.18, Lemmas 11.6, 11.11, 11.12, 11.13, 11.17, 11.36, 11.37, and the 4-regular completion of Proposition 11.38. The 16 + k count and the numerical part of Corollary 11.8 are also proved.

Second pass ([BRIEF2.md](BRIEF2.md), [REPORT2.md](REPORT2.md)), also without any conjecture as a hypothesis: the double hole move `doubleHoleMove`, Theorem 11.44 (`theorem1144`, `theorem1144_maxDegree`, `theorem1144_girth`), Lemma 11.16 (`lemma1116`) and `small_components_at_least_twice`.

## Checked independently of Codex (2026-11-05)

- Deleted this project's build output and re-ran `lake build`: 3188 jobs, success.
- Re-ran `Se20Insertion/AxiomAudit.lean`: every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
- Searched the sources for `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `implemented_by`, `extern`: none.
- Read the definitions and the statements of the conjectures and of the main theorems against the documents.
- For the second pass: rebuilt from scratch (3207 jobs), re-ran `#print axioms` for the Theorem 11.44 family and `doubleHoleMove` (the same three axioms), repeated the keyword search, read the statements.
- Re-checked the example in [TRIANGLE_COUNTEREXAMPLE.json](TRIANGLE_COUNTEREXAMPLE.json) with separate code.

The proofs themselves were checked only by the Lean kernel, not read.

## Not done

General chains (k ≥ 2) of Theorem 11.7; the chain part of Corollary 11.8; Lemmas 11.19–11.25; the two-colour core criterion of NEW_DIRECTIONS 11.25.

## Build

Run `build.ps1` or `lake build` with the local Mathlib path in `lakefile.toml`; it needs `leanprover/lean4:v4.35.0-rc4`.

## Third pass (2026-11-05): colour-set cores

`ColourSetCore.lean`, `ColourSetPeeling.lean`, `ColourSetSpecialCases.lean` and `ColourSetCounting.lean` prove Theorem 11.47 (`colourSetInsertion`), its k = 2 and k = 19 cases, `strongColourable_of_conj1150` and Proposition 11.49 (`allGroupsFail_clique_sum`, `insertion_of_separable_sum`). See [REPORT3.md](REPORT3.md). The project was rebuilt independently of Codex; every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Lemma 11.48 and the bound 87 are not formalized yet. Conjectures 11.46, 11.50 and 11.51 are not proved.

## Fourth pass (2026-11-05): fan lemma

`ForestL2.lean`, `ChordalFan.lean`, `Neighbourhood87.lean` and `FanLemma.lean` prove chordality of L² of a forest (`forest_L2_chordal`), Lemma 11.48 with a weaker witness-forest hypothesis (`lemma1148`, `lemma1148_induced`), the cycle and girth consequences (`longChain_cycle`, `longChain_girth`, `longChain_girth_half`) and the bound 87 for Δ ≤ 4, girth ≥ 7 (`neighbourhood_edges_le_87`, `directPairs_le_87`). See [REPORT4.md](REPORT4.md), which leads with the corrections to the paper wording. Rebuilt independently with exit code 0; all 87 audited declarations use only `propext`, `Classical.choice`, `Quot.sound` ([AXIOMS4.txt](AXIOMS4.txt)).

## Fifth and sixth passes (2026-11-06)

[REPORT5.md](REPORT5.md) and [REPORT6.md](REPORT6.md) add almost everything still open in section 11 of the log: general chains of Theorem 11.7, Corollary 11.8, 11.19–11.25, 11.28, the gain formula, 11.39–11.41, 11.1, 11.2, 11.4, 11.5, 11.10, the core theorem and the ratio (2K − d)/d for arbitrary K, the identity P2, the hole-move formula. Not done: Gallai's theorem for 11.40(5) (a seventh pass is working on it), and a geometric construction of the map in `sixty_six_chains`.

Checked independently of Codex: sources copied to an empty directory and rebuilt without Lake (exit code 0, 68 modules); no `sorry`, no `native_decide`, no project axiom; [AXIOMS6.txt](AXIOMS6.txt) holds the single-line audit results, which are only the three standard axioms, and the multi-line ones are the same three in the log. `Proposition1133` appears only as a named hypothesis. The proofs were checked only by the Lean kernel, not read.
