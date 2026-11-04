# Second pass: formalize the counting theorem 11.44

Your first report was checked: the rebuild, `#print axioms`, the keyword search and your example for Lemma 11.17 were re-run independently and agree, and the documents were corrected. Thank you for catching the flaw. The same working rules as `BRIEF.md` apply (this directory only, no pushes, nothing on drive C, at most 6 processes, one Mathlib-importing Lean process at a time ideally, no `sorry`, `admit`, new `axiom`, `native_decide`, `ofReduceBool`). Do not overwrite `REPORT.md`; write `REPORT2.md`. Keep the existing theorems building. Put new work in new files and add them to `build.ps1` and `AxiomAudit.lean`.

Read section 11.24 of the current documents. A fresh copy is at `reference\NEW_DIRECTIONS_zh.md`: section "11.24", "洞的连走" and "定理 11.44". Be adversarial: an independent reader found no mathematical error, but it has never been formalized. Report anything wrong, however small.

## Part 1: the double hole move

Let `φ` be a partial colouring of `L2 G` with coloured set `F`, `g ∉ F`, and `f, w ∈ F` with `f` adjacent to `g`, `w` adjacent to `f`, `g ≠ w`, `g` and `w` non-adjacent in `L2 G`. Let `a = colour f`, `b = colour w`. If `f` is the only `a`-neighbour of `g`, `f` the only `a`-neighbour of `w`, and `w` the only `b`-neighbour of `f`, then there is a partial colouring with coloured set `insert g F`. State it with exactly these hypotheses and prove it for any `G`, without a degree or girth assumption if none is needed.

## Part 2: Theorem 11.44

Let `G` be a finite simple 4-regular graph with girth at least 7 (use Mathlib's girth notion, or an explicit "no cycle of length at most 6"; say which, and prove your form is what Mathlib's notion gives if you use your own). Let `h` be an edge and `φ` a partial colouring of `L2 G` with coloured set `univ \ {h}`. Then there is no `R : Finset G.edgeSet` with `h ∈ R` such that

- (a) every `x ∈ R` sees every colour except its own (`h` sees all 20);
- (b) if `x ∈ R`, `y` is coloured and adjacent to `x`, and `y` is the only neighbour of `x` with its colour, then `y ∈ R`;
- (c) there are no `g ∈ R`, `f`, `w` as in Part 1 for this `φ`.

Note: `g` in (c) may be coloured, so state a version of the Part 1 configuration for arbitrary `g`, with singleness read in `φ`. Do not assume that a hole can actually reach `g`; (c) is a statement about `φ` alone. Do not strengthen or weaken (a), (b), (c).

Proof outline; the document has details. With `R' = R \ {h}`, `M = |N(h) ∩ R'|`:
- For `x ∈ R'`: `d(x)` coloured conflicts (24, or 23 if `x` conflicts with `h`), `t(x)` coloured neighbours outside `R`, `r(x) = d(x) - t(x)`, `ns(x)` neighbours non-single at `x`, so `ns(x) ≤ 2(d(x) - 19)`; `y(x)` is the number of `z ∈ N(x) ∩ R'` with the colour of `x` non-single at `z`.
- By (b): `Σt + Σy ≤ Σns ≤ 10|R'| - 2M`.
- Conflict pairs inside `R'` are `Σr/2`; a pair that is not mutually single contributes to `y`; so mutually single pairs `U` satisfy `2U ≥ Σr - 2Σy`.
- With `c(f)` the number of mutually single partners, `s(f) = y(f) + t(f)`, `N₁(f)` the neighbours in `R'` at which the colour of `f` is single: (c) gives `N₁(f) ⊆ N[w]` for each partner `w`. Girth at least 7 gives `|N(f) ∩ N[w]| = 15` if `f, w` share an endpoint, `6` otherwise. Hence `c(f) ≤ s(f)/3`, or `(s(f)+1)/3` if `f` conflicts with `h`.
- Summing: `24|R'| ≤ (7/3)Σy + (4/3)Σt + (4/3)M < 24|R'|`. `R'` is nonempty because `h` is blocked and has at most 24 conflicts.

## Part 3 (if time remains): supporting facts

- Lemma 11.16: at least `7m` components over the 190 pairs for `m` coloured edges, in the form needed for any partial colouring with each edge having at most 24 conflicts.
- `2n₁ + n₂ ≥ 2m`, where `n₁, n₂` count components of sizes 1 and 2.

## `REPORT2.md`

Lead with any flaw. Then the exact Lean statements, files, exact `#print axioms` output, what remains unproved, what was not done. Stop when Parts 1 and 2 build; spend at most about 2 more hours on Part 3.
