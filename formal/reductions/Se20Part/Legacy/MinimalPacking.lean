module

public import Se20Part.Legacy.Packing
public import Se20Part.Legacy.Bounds.ConflictDegree

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Only the clique bounds needed for 20-packing. The maximum-degree bound is
supplied separately, and the last field requires 15 rather than 7.
The original `CliqueThresholds20` and its theorems are unchanged. -/
structure MinimalCliqueBounds20 : Prop where
  high20 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 20 ≤ H.degree x) → Q.card ≤ 19
  high21 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 21 ≤ H.degree x) → Q.card ≤ 18
  high22 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 22 ≤ H.degree x) → Q.card ≤ 17
  high23 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 23 ≤ H.degree x) → Q.card ≤ 16
  high24 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 24 ≤ H.degree x) → Q.card ≤ 15

omit [DecidableEq W] in
theorem minimalCliqueBounds20_of_thresholds (ht : CliqueThresholds20 H) :
    MinimalCliqueBounds20 H where
  high20 := ht.high20
  high21 := ht.high21
  high22 := ht.high22
  high23 := ht.high23
  high24 Q hc hd := (ht.high24 Q hc hd).trans (by omega)

theorem local20_of_minimal_clique_bounds (hdegree : ∀ x, H.degree x ≤ 24)
    (hb : MinimalCliqueBounds20 H) (M : Finset W) (hM : IsOptimal H M)
    {v : W} (hv : v ∈ M) :
    H.degree v + 1 + (privateFinset H M v).card ≤ 40 := by
  classical
  have hc : H.IsClique (↑(privateFinset H M v) : Set W) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx)
      ((mem_privateFinset H M v y).mp hy) hxy
  have hm : ∀ x ∈ privateFinset H M v, H.degree v ≤ H.degree x := by
    intro x hx
    exact private_degree_mono H M hM hv ((mem_privateFinset H M v x).mp hx)
  by_cases hlow : H.degree v ≤ 19
  · have := private_card_le_degree_add_one H M v
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

theorem packing20_of_minimal_clique_bounds (hdegree : ∀ x, H.degree x ≤ 24)
    (hb : MinimalCliqueBounds20 H) :
    ∃ M : Finset W, H.IsMaximumIndepSet M ∧ Fintype.card W ≤ 20 * M.card := by
  obtain ⟨M, hM⟩ := optimal_exists H
  exact ⟨M, hM.1, packing_of_local_bound H M hM.1 20
    (fun v hv => local20_of_minimal_clique_bounds H hdegree hb M hM hv)⟩

theorem minimalCliqueBounds20_induce (hb : MinimalCliqueBounds20 H)
    (F : Set W) [DecidablePred (· ∈ F)] : MinimalCliqueBounds20 (H.induce F) where
  high20 := clique_bound_induce H F 20 19 hb.high20
  high21 := clique_bound_induce H F 21 18 hb.high21
  high22 := clique_bound_induce H F 22 17 hb.high22
  high23 := clique_bound_induce H F 23 16 hb.high23
  high24 := clique_bound_induce H F 24 15 hb.high24

theorem subset_packing20_of_minimal_clique_bounds (hdegree : ∀ x, H.degree x ≤ 24)
    (hb : MinimalCliqueBounds20 H) (F : Finset W) :
    ∃ M : Finset W, M ⊆ F ∧ H.IsIndepSet (M : Set W) ∧ F.card ≤ 20 * M.card := by
  classical
  let S : Set W := F
  let : Fintype S := Subtype.fintype (fun x => x ∈ S)
  have hbS : MinimalCliqueBounds20 (H.induce S) := minimalCliqueBounds20_induce H hb S
  have hdS : ∀ x : S, (H.induce S).degree x ≤ 24 :=
    fun x => (induced_degree_le H S x).trans (hdegree x.val)
  obtain ⟨N, hN, hcount⟩ := packing20_of_minimal_clique_bounds (H.induce S) hdS hbS
  refine ⟨N.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact y.property
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact hN.isIndepSet ha hb (fun heq => hxy (congrArg Subtype.val heq))
  · have hcardS : Fintype.card S = F.card := Fintype.card_of_subtype F (fun _ => Iff.rfl)
    simpa only [card_image_of_injective N Subtype.val_injective, hcardS] using hcount

/-- C4 is discharged by the original maximum-degree hypothesis. The five
remaining clique bounds are still explicit and are not asserted here. -/
theorem induced_matching_packing20_of_minimal_clique_bounds
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel (conflictGraph G).Adj]
    (hΔ : ∀ x, G.degree x ≤ 4) (hb : MinimalCliqueBounds20 (conflictGraph G))
    (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card := by
  simpa only [conflictGraph_independent_iff] using
    subset_packing20_of_minimal_clique_bounds (conflictGraph G)
      (conflict_degree_le_24 G hΔ) hb F

end Se20Part.Legacy
