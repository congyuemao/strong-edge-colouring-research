# Lean: Part I of the manuscript (large girth)

Work by Codex from [BRIEF.md](BRIEF.md), [BRIEF2.md](BRIEF2.md), [BRIEF3.md](BRIEF3.md) in `E:\lean\se20-girth`; its own account is [REPORT.md](REPORT.md), which leads with the flaws it found. Cited theorems are explicit hypotheses (`Kostochka`, `Haxell`), never axioms.

Proved in Lean, with `Kostochka` as the only hypothesis: `theorem_A`, `theorem_B_prime`, `theorem_B_double_prime`, `theorem_B_of_kostochka` (girth at least 39360), `theorem_B_plus_of_kostochka` (girth at least 5710), `proposition_3_13`.

Proved with no hypothesis: `haxell`, `lovasz_local_lemma`, `exp31_transfer_bound`, `transfer_spanning_family_bound`, Lemmas 3.1, 3.2, 3.6, 3.9, 3.11, 3.15, Remark 3.3, Corollary 3.10, the tagged Haxell remark, ball counts in finite graphs and on the infinite 4-regular tree.

`Kostochka` is the statement of the 1978 theorem as a `def ... : Prop`, a parameter of the theorems. It is not proved here.

Checked independently of Codex: sources copied to an empty directory and rebuilt (exit code 0, 57 modules; the first attempts failed reading Mathlib `.olean` files under memory pressure, so the script retries on that error only). No `sorry`, `native_decide` or project axiom. All audited declarations depend on at most `propext`, `Classical.choice`, `Quot.sound` ([AXIOMS.txt](AXIOMS.txt)). The statements of `theorem_B`, `theorem_B_plus_of_kostochka`, `haxell`, `Kostochka`, `Haxell`, `StrongColourable`, `GirthAtLeast` were read. The proofs were checked only by the Lean kernel, not read.

Build: `build.ps1`, Lean `v4.35.0-rc4`, Mathlib from the local path in `lakefile.toml`.
