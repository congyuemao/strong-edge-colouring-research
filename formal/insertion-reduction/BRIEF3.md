# Third pass: formalize the colour-set core theorem (section 11.26)

Read section 11.26 of `reference\NEW_DIRECTIONS_zh.md` ("颜色组核", 定理 11.47, 引理 11.48, 命题 11.49). It has had no outside review. Be adversarial: if any statement is false as written or a proof has a gap, say so at the top of the report, with a concrete example if you have one, and prove the corrected statement. Build on the existing `Se20Insertion` library and its definitions. No `sorry`, no new axioms. Do not change existing theorem statements.

## Part 1: Theorem 11.47

Let `H` be a finite graph on `W` (later `L2 G`), `φ` a partial colouring with coloured set `F`, `h ∉ F`, and `Y` a set of at least 2 colours. Work in `F ∪ {h}`; neighbours in `U`, the set of edges outside `F ∪ {h}`, simply do not count.

- `TangledAt v a b`: some `a`-neighbour and some `b`-neighbour of `v` lie in one `(a, b)` Kempe component of `φ`.
- `S_Y`: the `v ∈ F ∪ {h}` not coloured from `Y` (`h` counts as not coloured from `Y`) at which every pair of distinct colours of `Y` is tangled.
- `τ_Y v = 2 * (20 - |Y|) + d_Y v - deg v`, computed in integers, where `deg v` is the number of neighbours of `v` in `F ∪ {h}` and `d_Y v` the number of those coloured from `Y`.

State: if for every `C ⊆ S_Y` with `h ∈ C` there is `v ∈ C` with `|N(v) ∩ C| < τ_Y v` (this is exactly `h ∉ C_Y`; also state the equivalence with the peeling definition if it is cheap), then `φ` extends to a proper colouring of `F ∪ {h}`.

A cleaner proof than the rank argument in the document, which you may use: suppose there is no extension. Let `C` be the set of `v` such that some proper colouring `ψ` of `(F ∪ {h}) \ {v}` has the same colour classes as `φ` on every colour of `Y`. Then `h ∈ C`. For `v ∈ C` with witness `ψ`: `v` is not coloured from `Y` in `φ`, the `Y` classes and hence tangling are unchanged. If a pair of `Y` were not tangled at `v`, a Kempe swap in that pair frees a colour, giving an extension, so `v ∈ S_Y`. All colours are seen at `v`, so at least `τ_Y v` neighbours carry a colour outside `Y` single at `v`, and moving the hole to any of them keeps the `Y` classes, so those neighbours lie in `C`. Hence `|N(v) ∩ C| ≥ τ_Y v` for all `v ∈ C`, contradicting the hypothesis. Note that the extension is obtained for the state itself: state whether it also keeps `F` coloured (it does, as a colouring of `F ∪ {h}`, not as an extension of `φ` on `F`; recolouring is allowed, so "extends" means "there is a proper colouring of `F ∪ {h}`").

## Part 2: special cases and the implication chain

- `k = 2` gives the two-colour core criterion.
- `k = 19`: when `h` has no separable pair and colour `u` is single at `h` on `f_u`, with `Y` the other 19 colours, `h ∉ C_Y` iff `f_u` has a separable pair `(a, b)` with `a, b ≠ u`. Hence the conclusion of Theorem 11.7 follows from Theorem 11.47 in the single-colour case.
- Conjecture 11.50 as a `def`: every star state has some `Y` with `h ∉ C_Y`. Prove `conj1150 → ` the existing star insertion hypothesis `→ StrongColourable` via `strongColourable_of_starInsertion`, for simple graphs of maximum degree at most 4. Check the hypothesis shape carefully; state exactly what is needed.

## Part 3: Proposition 11.49

Assume `deg h = 24` and `h ∈ C_Y` for all `Y` with `|Y| = k`, `2 ≤ k ≤ 19`.
1. Every pair of colours is tangled at `h`.
2. `Σ_{f ∈ N(h)} K_k(f) ≥ (2/3) · 24 · C(19, k)`, stated without division: `3 * Σ ≥ 2 * 24 * C(19, k)`, where `K_k(f)` counts the `k`-sets `Y` with `φ(f) ∉ Y` and every pair of `Y` tangled at `f`. Use `Σ_Y |Y ∩ colours of neighbours|`-style double counting.
3. A colour single at `h` sits on an edge seeing all 19 other colours.
4. `2 d_Y(v) ≤ 2 deg v - 2(20 - k)` on the core, and `d_Y v ≥ k`.

Also prove Conjecture 11.51's implication: for `k = 2`, if the sum of separable pairs over `N(h)` exceeds 1368 then not every pair fails.

## Part 4 (if time remains): Lemma 11.48

`L2` of a tree is chordal, in the form needed: if `v` and an `(a, b)` shortest path `P` from an `a`-neighbour to a `b`-neighbour of `v` satisfy the tree hypothesis of Lemma 11.48, every vertex of `P` is adjacent to `v`. Then: at girth at least 7 and 4-regular, `|E(L2[N(v)])| = 87`, or at least `≤ 87`. If a full proof of chordality is out of reach, say what was proved. A long-chain lower bound `|P| ≥ g/2 - 1` is welcome.

## `REPORT3.md`

Lead with any flaw. Then exact Lean statements, files, exact `#print axioms` output (update `AxiomAudit.lean`), what remains unproved, what was not done. Build with the existing `build.ps1`. Stop when Parts 1–3 build, or report exactly what blocks them.
