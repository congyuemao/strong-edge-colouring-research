# Lean: Part I of the manuscript (large girth)

Work by Codex from [BRIEF.md](BRIEF.md), [BRIEF2.md](BRIEF2.md), [BRIEF3.md](BRIEF3.md) in `E:\lean\se20-girth`; its own account is [REPORT.md](REPORT.md), which leads with the flaws it found. Cited theorems are explicit hypotheses (`Kostochka`, `Haxell`), never axioms.

Proved in Lean: Lemmas 3.1, 3.2, 3.6, 3.9, 3.11, 3.15; Remark 3.3; Corollary 3.10; Proposition 3.13; the tagged Haxell remark; the finite asymmetric local lemma (`lovasz_local_lemma`); `theorem_A` (hypothesis `Kostochka`); `theorem_B_prime`, `theorem_B_double_prime` (`Kostochka`); `theorem_B` (`Kostochka`, `Haxell`). `theorem_B_plus` is conditional on `Kostochka` and two transfer-matrix hypotheses, which are named in the theorem; a third pass is working on them.

Checked independently of Codex: copied the sources to an empty directory and rebuilt with `build.ps1` (exit code 0; a first attempt failed on reading one Mathlib `.olean` while other builds were running, and the rerun passed), read the statements of `theorem_B`, `Kostochka`, `Haxell`, `StrongColourable`, `GirthAtLeast`. Every audited declaration depends on at most `propext`, `Classical.choice`, `Quot.sound` ([AXIOMS.txt](AXIOMS.txt)). The audit does not cover the hypotheses. The proofs were checked only by the Lean kernel, not read.

Build: `build.ps1`, Lean `v4.35.0-rc4`, Mathlib from the local path in `lakefile.toml`.
