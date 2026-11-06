# Fourth pass: what the third pass left

Read `REPORT.md` (Third pass, "Remaining proof obligations"). Same rules: no `sorry`, no new axioms, no `native_decide`, no change to proved statements, nothing weakened silently, cited theorems only as named hypotheses, flaws first. Memory on this machine is tight: at most one `lean` process at a time, `-j1`, and the build guard in `build.ps1` stays on. Another Codex run is working on Gallai's degree-choosability theorem in `E:\lean\se20-insertion`; do not duplicate it: take its statement as a named hypothesis `GallaiDegreeChoosable` for now wherever A03, A04 need it.

There is time: do not stop at a partial result while a target can still be attacked. Order:

1. G12 in full (construction of compatible source and target colours, the exceptional five-cut choice, endpoint counts, the minimal-counterexample connectivity arguments).
2. G13, then the rest of G14 (incident edges, support case), G16.
3. G05: replace the three huge abstract checks by the actual route of the source files: the maximum-matching D/A/C decomposition (Gallai-Edmonds, or the form needed, on the complement) with factor-critical odd blocks, the small-saving cases for orders at most 25, the five-bag classification at order 41. Each finite residual that is small may be kernel-checked; list what remains.
4. A03, A04, A02, A06.
5. The rest of F09, F03, F04, F05, F07, then S02, S06, S07, S08, S17, S19.

Append a section "Fourth pass" to `REPORT.md`; update `AxiomAudit.lean`, `build.ps1`. Before finishing, run the whole `build.ps1` so that `AxiomAudit` and the root module compile together (the last pass left a name clash that only the final link step showed; `local instance : DecidableEq G.edgeSet` needs a unique name in each module that is imported into the audit).
