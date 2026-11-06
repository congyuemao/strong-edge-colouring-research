# Fifth pass: the rest of the older results

Read `REPORT.md` (Fourth pass, remaining obligations). Same rules: no `sorry`, no new axioms, no `native_decide`, no change to proved statements, nothing weakened silently, cited theorems only as named hypotheses, flaws first. Use `-j1`. Other Lean jobs may run; do not wait for them and do not stop or ask: retry with a delay. Only stop when the targets are done or each one is honestly blocked.

Gallai's degree-list theorem is now proved in the sister project: `E:\lean\se20-insertion\Se20Insertion\Gallai.lean` with its imports (`DegreeListTools`, `DegreeListReduction`, `DegreeListInduced`, `DegreeListBrooks`, `FiniteNonseparating`, `RegularCycle`, `NonseparatingPair`). Copy them into this project and replace any `GallaiDegreeChoosable` hypothesis by the theorem.

Order: A03, A04, A02, A06; G13; G16 (with G15 as a named hypothesis, or prove G15 with the polynomial method only if a kernel check of the coefficient 12240 is feasible); G05's real route (D/A/C decomposition, factor-critical blocks, small-saving cases, five-bag classification at order 41); then F09, F03, F04, F05, F07; then S02, S06, S07, S08, S17, S19. Run the whole build at the end, and append "Fifth pass" to `REPORT.md`.
