# Second pass: remove the LP hypothesis, then try to discharge Proposition D

Your first report was checked: the Lean build, `#print axioms`, the SHA256 of `d16.cnf` and `check_lrat.exe` on the certificate were all
re-run independently and agree. Thank you for the normalization catch in Lemma B. The same working rules as `BRIEF.md` apply
(this directory only, no pushes, nothing installed on drive C, at most 6 processes, ideally one Mathlib-importing Lean process at once, no `sorry`, `admit`, new `axiom`).
Git metadata is read-only in your sandbox; do not try to commit, I will. Write the result to `REPORT2.md`, and do not overwrite `REPORT.md`.

## Part 1 (the main job): Lemma A without LP duality

`FractionalDuality` is not needed. Lemma A has an elementary proof by Reed's process. Formalize it in a new file
`Se20Fractional/LocalReedElementary.lean`, then add to `TheoremF.lean`:

```text
theorem theorem_F_of_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : PropositionD G) : FractionalColourable (L2 G) 20
```

Keep the existing conditional theorem. `#print axioms theorem_F_of_D` must show only `propext`, `Classical.choice`, `Quot.sound`. Check the proof below as adversarially as the first one; report any flaw.

**Key inequality.** Let U be a finite vertex set, 𝒮 the family of maximum-cardinality stable subsets of U, v ∈ U, and ω(v) ≥ 1 an upper bound on the size of cliques within U containing v. Then

Σ_{S∈𝒮} |S ∩ N_U(v)| + (ω(v) + 1) · |{S ∈ 𝒮 : v ∈ S}| ≥ 2 |𝒮|.

Proof. Let 𝒮_v = {S ∈ 𝒮 : v ∈ S} and 𝒮₁ = {S ∈ 𝒮 : v ∉ S, |S ∩ N_U(v)| = 1}.
- If S ∌ v then S ∩ N_U(v) ≠ ∅, otherwise S + v is a larger stable set.
- So the left side is at least |𝒮₁| + 2 |𝒮 − 𝒮_v − 𝒮₁| + (ω + 1) |𝒮_v| = 2|𝒮| − |𝒮₁| + (ω − 1)|𝒮_v|, and it suffices that |𝒮₁| ≤ (ω − 1)|𝒮_v|.
- Map S ∈ 𝒮₁ with S ∩ N_U(v) = {u} to S' = S − u + v. S' is stable of the same size, so S' ∈ 𝒮_v, and S = S' − v + u recovers S from (S', u).
- For a fixed S', the possible u are pairwise adjacent: if u₁, u₂ are non-adjacent then S' − v + u₁ + u₂ is a larger stable set. They are all adjacent to v, so together with v they form a clique in U. Hence each S' has at most ω(v) − 1 preimages.

**Weighted statement, by strong induction on |U|.** Let r : V → ℝ be nonnegative on U and k real, with

Σ_{u∈N_U(v)} r(u) + (ω(v) + 1) r(v) ≤ 2k for all v ∈ U

(ω as above, for U). Then there is a family of stable subsets of U, with nonnegative weights of total ≤ k, that covers each v ∈ U with weight ≥ r(v). (For U empty, or r ≡ 0, take k ≥ 0 into account: state whichever normalization is cleanest; the application has r ≡ 1 and k = 20.)

Induction step. Discard vertices with r = 0 first if that helps. Let p(x) = |{S ∈ 𝒮 : x ∈ S}| / |𝒮|. Take ε = min over x with p(x) > 0 of r(x)/p(x), attained at v₀. Give each S ∈ 𝒮 weight ε/|𝒮|. Put r' = r − εp ≥ 0 and U' = {x ∈ U : r'(x) > 0}, a proper subset of U since r'(v₀) = 0.
- For v ∈ U', the key inequality gives Σ_{u∈N_{U'}(v)} r'(u) + (ω'(v) + 1) r'(v) ≤ 2k − ε·(key sum)/|𝒮| ≤ 2(k − ε), where ω' ≤ ω is the clique bound restricted to U' (or keep using ω, which is still an upper bound). So induction applies to U' with k' = k − ε, and k' ≥ 0 because the left side is nonnegative. The total is ε + k' = k.
- If U' is empty: at v₀, r(v₀) = εp(v₀) and r(u) ≥ εp(u) for all u, so 2k ≥ ε·(key sum at v₀)/|𝒮| ≥ 2ε, i.e. ε ≤ k.

**Application.** r ≡ 1, ω(u) = 15, k = 20 on each U in the existing `theorem_F` induction, exactly as now, using `peeling`, `hD` and `l2_degree_le_24`.

## Part 2 (stretch; only after Part 1 builds): discharge `hD`

Try to prove `PropositionD G` for every `G` with `∀ v, G.degree v ≤ 4`, in a separate file, connecting a concrete CNF to the graph statement through a Lean-proved reduction and the verified LRAT checker in `Std.Tactic.BVDecide.LRAT`.
- Here, and only here, using `Lean.ofReduceBool` (through `native_decide` or the `bv_decide`/`bv_check` machinery) is allowed, because a 478 MB certificate cannot be reduced by the kernel. Isolate it so that `theorem_F_of_D` stays free of it, name the unconditional result `theorem_F_unconditional`, and report its `#print axioms` output exactly.
- You may change the encoding if a smaller certificate or a simpler soundness proof helps. For scale, `C:\Users\21161\Documents\ChatGPT\se20-ideas\exp49_frac_core.py` solves in about 30 s with CaDiCaL against about 360 s for yours, thanks to double-lex symmetry breaking on the T-by-(A, B) matrix; you audited it already. Fewer auxiliary variables, or a lazily generated clause set, may also be easier to prove sound.
- The hard parts are restricting to G[V(Q)], the embedding into a fixed vertex type, the relabelling that justifies the symmetry breaking, and the Tseitin and counter gates. Prove them, do not assume them.
- Spend at most about 3 hours of wall-clock time on Part 2 (check with `Get-Date`). If it does not close, leave the partial files out of the default build target, say how far it got and what is missing, and stop. A partial result reported honestly is fine; a hidden assumption is not.

## `REPORT2.md`

Lead with any flaw found. Then: exact theorem statements proved, exact `#print axioms` output for `theorem_F_of_D` (and `theorem_F_unconditional` if it exists), what remains a hypothesis, what was not done.
