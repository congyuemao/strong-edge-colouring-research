# Lean: Part II and the older structural results

Work by Codex from [BRIEF.md](BRIEF.md), [BRIEF2.md](BRIEF2.md) in `E:\lean\se20-reductions`; its own account is [REPORT.md](REPORT.md), which leads with the flaws it found and lists what is not done. Cited theorems are explicit hypotheses (`Brooks`, `Haxell`, `JoosNguyen`).

This is a partial formalization. See the table in REPORT.md: Lemmas 4.1 (degree part), 4.2, 4.4, 4.5 (without Cameron), 4.12, item 5.7, triangle reducibility, the local-injection pull-back and the Lovasz partition argument are proved; a second pass is working on the rest.

Checked independently of Codex: sources copied to an empty directory and rebuilt with `build.ps1` (exit code 0); 52 audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound` ([AXIOMS.txt](AXIOMS.txt)). The audit does not cover the hypotheses. The proofs were checked only by the Lean kernel, not read.
