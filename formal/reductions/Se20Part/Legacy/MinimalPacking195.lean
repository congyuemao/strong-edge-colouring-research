module

public import Se20Part.Legacy.MinimalPacking

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The five stronger bounds required for 19.5-packing. Neither these bounds
nor the separate exclusion of twenty-cliques is asserted unconditionally. -/
structure CliqueBounds195 : Prop where
  high20 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 20 ≤ H.degree x) → Q.card ≤ 18
  high21 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 21 ≤ H.degree x) → Q.card ≤ 17
  high22 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 22 ≤ H.degree x) → Q.card ≤ 16
  high23 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 23 ≤ H.degree x) → Q.card ≤ 15
  high24 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 24 ≤ H.degree x) → Q.card ≤ 14

/-- Degree nineteen needs the separate clique-size hypothesis. -/
theorem local39_of_clique_bounds
    (hdegree : ∀ x, H.degree x ≤ 24) (hb : CliqueBounds195 H)
    (no20 : ∀ Q : Finset W, H.IsClique (Q : Set W) → Q.card ≤ 19)
    (M : Finset W) (hM : IsOptimal H M) {v : W} (hv : v ∈ M) :
    H.degree v + 1 + (privateFinset H M v).card ≤ 39 := by
  classical
  have hc : H.IsClique (↑(privateFinset H M v) : Set W) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx)
      ((mem_privateFinset H M v y).mp hy) hxy
  have hm : ∀ x ∈ privateFinset H M v, H.degree v ≤ H.degree x := by
    intro x hx
    exact private_degree_mono H M hM hv ((mem_privateFinset H M v x).mp hx)
  by_cases hlow : H.degree v ≤ 18
  · have := private_card_le_degree_add_one H M v
    omega
  by_cases h19 : H.degree v = 19
  · have := no20 _ hc
    omega
  have hmax := hdegree v
  by_cases h20 : H.degree v = 20
  · have := hb.high20 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h21 : H.degree v = 21
  · have := hb.high21 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h22 : H.degree v = 22
  · have := hb.high22 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h23 : H.degree v = 23
  · have := hb.high23 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  have := hb.high24 _ hc (fun x hx => by have := hm x hx; omega)
  omega

/-- T1: a conditional theorem for an arbitrary finite graph, retaining the
integer inequality and a maximum independent-set witness. -/
theorem packing195_of_clique_bounds
    (hdegree : ∀ x, H.degree x ≤ 24) (hb : CliqueBounds195 H)
    (no20 : ∀ Q : Finset W, H.IsClique (Q : Set W) → Q.card ≤ 19) :
    ∃ M : Finset W, H.IsMaximumIndepSet M ∧
      2 * Fintype.card W ≤ 39 * M.card := by
  obtain ⟨M, hM⟩ := optimal_exists H
  refine ⟨M, hM.1, ?_⟩
  have hcount := private_double_count H M hM.1
  have hsum := sum_le_sum (fun v hv =>
    local39_of_clique_bounds H hdegree hb no20 M hM hv)
  simp only [sum_const, smul_eq_mul] at hsum
  omega

/-- Full-graph threshold bounds transfer to induced subgraphs using degree
monotonicity. No edges of the ambient graph are deleted before forming H. -/
theorem cliqueBounds195_induce (hb : CliqueBounds195 H)
    (F : Set W) [DecidablePred (· ∈ F)] : CliqueBounds195 (H.induce F) where
  high20 := clique_bound_induce H F 20 18 hb.high20
  high21 := clique_bound_induce H F 21 17 hb.high21
  high22 := clique_bound_induce H F 22 16 hb.high22
  high23 := clique_bound_induce H F 23 15 hb.high23
  high24 := clique_bound_induce H F 24 14 hb.high24

/-- Excluding twenty-cliques also passes to every induced subgraph. -/
theorem clique_card_le_nineteen_induce
    (no20 : ∀ Q : Finset W, H.IsClique (Q : Set W) → Q.card ≤ 19)
    (F : Set W) [DecidablePred (· ∈ F)]
    (Q : Finset F) (hQ : (H.induce F).IsClique (Q : Set F)) : Q.card ≤ 19 :=
  clique_bound_induce H F 0 19 (fun R hR _ => no20 R hR) Q hQ
    (fun _ _ => Nat.zero_le _)

/-- Candidate-set form: only cliques contained in F must have size at most
nineteen. The ambient graph may contain twenty-cliques outside F. -/
theorem subset_packing195_of_clique_bounds
    (hdegree : ∀ x, H.degree x ≤ 24) (hb : CliqueBounds195 H)
    (F : Finset W)
    (no20 : ∀ Q : Finset W, Q ⊆ F → H.IsClique (Q : Set W) → Q.card ≤ 19) :
    ∃ M : Finset W, M ⊆ F ∧ H.IsIndepSet (M : Set W) ∧
      2 * F.card ≤ 39 * M.card := by
  classical
  let S : Set W := F
  let : Fintype S := Subtype.fintype (fun x => x ∈ S)
  have hbS : CliqueBounds195 (H.induce S) := cliqueBounds195_induce H hb S
  have hdS : ∀ x : S, (H.induce S).degree x ≤ 24 :=
    fun x => (induced_degree_le H S x).trans (hdegree x.val)
  have hnS : ∀ Q : Finset S, (H.induce S).IsClique (Q : Set S) → Q.card ≤ 19 := by
    intro Q hQ
    have hs : Q.image Subtype.val ⊆ F := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      exact y.property
    have hc : H.IsClique (↑(Q.image Subtype.val) : Set W) := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
      exact hQ ha hb (fun heq => hxy (congrArg Subtype.val heq))
    simpa only [card_image_of_injective Q Subtype.val_injective] using no20 _ hs hc
  obtain ⟨N, hN, hcount⟩ := packing195_of_clique_bounds (H.induce S) hdS hbS hnS
  refine ⟨N.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact y.property
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact hN.isIndepSet ha hb (fun heq => hxy (congrArg Subtype.val heq))
  · have hcardS : Fintype.card S = F.card := Fintype.card_of_subtype F (fun _ => Iff.rfl)
    simpa only [card_image_of_injective N Subtype.val_injective, hcardS] using hcount

/-- T2: conflicts are evaluated in the complete original graph G. The stronger
threshold record and exclusion of candidate twenty-cliques remain hypotheses. -/
theorem induced_matching_packing195_of_clique_bounds
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel (conflictGraph G).Adj]
    (hΔ : ∀ x, G.degree x ≤ 4) (hb : CliqueBounds195 (conflictGraph G))
    (F : Finset G.edgeSet)
    (no20 : ∀ Q : Finset G.edgeSet, Q ⊆ F →
      (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      2 * F.card ≤ 39 * M.card := by
  simpa only [conflictGraph_independent_iff] using
    subset_packing195_of_clique_bounds (conflictGraph G)
      (conflict_degree_le_24 G hΔ) hb F no20

end Se20Part.Legacy
