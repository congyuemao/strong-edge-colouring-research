module

public import Se20Part.Legacy.Conflict
public import Se20Part.Legacy.DoubleCount

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A clique bound using ambient degrees passes to every induced subgraph. -/
theorem clique_bound_induce (F : Set W) [DecidablePred (· ∈ F)] (k b : ℕ)
    (hbound : ∀ Q : Finset W, H.IsClique (Q : Set W) →
      (∀ x ∈ Q, k ≤ H.degree x) → Q.card ≤ b)
    (Q : Finset F) (hQ : (H.induce F).IsClique (Q : Set F))
    (hdeg : ∀ x ∈ Q, k ≤ (H.induce F).degree x) : Q.card ≤ b := by
  classical
  let R := Q.image Subtype.val
  have hc : H.IsClique (R : Set W) := by
    intro x hx y hy hxy
    change x ∈ Q.image Subtype.val at hx
    change y ∈ Q.image Subtype.val at hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact hQ ha hb (fun heq => hxy (congrArg Subtype.val heq))
  have hd : ∀ x ∈ R, k ≤ H.degree x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (hdeg y hy).trans (induced_degree_le H F y)
  have hr := hbound R hc hd
  simpa only [R, card_image_of_injective Q Subtype.val_injective] using hr

theorem thresholds20_induce (ht : CliqueThresholds20 H)
    (F : Set W) [DecidablePred (· ∈ F)] : CliqueThresholds20 (H.induce F) where
  max_degree v := (induced_degree_le H F v).trans (ht.max_degree v.val)
  high20 := clique_bound_induce H F 20 19 ht.high20
  high21 := clique_bound_induce H F 21 18 ht.high21
  high22 := clique_bound_induce H F 22 17 ht.high22
  high23 := clique_bound_induce H F 23 16 ht.high23
  high24 := clique_bound_induce H F 24 7 ht.high24

/-- Every candidate vertex set has a large independent subset under explicit thresholds. -/
theorem subset_packing20_of_thresholds (ht : CliqueThresholds20 H) (F : Finset W) :
    ∃ M : Finset W, M ⊆ F ∧ H.IsIndepSet (M : Set W) ∧ F.card ≤ 20 * M.card := by
  classical
  let S : Set W := F
  let : Fintype S := Subtype.fintype (fun x => x ∈ S)
  have hthreshold : CliqueThresholds20 (H.induce S) := thresholds20_induce H ht S
  obtain ⟨N, hN, hcount⟩ := packing20_of_thresholds (H.induce S) hthreshold
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

/-- Original-edge formulation; proving these full-conflict-graph thresholds is still required. -/
theorem induced_matching_packing20_of_thresholds {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    [DecidableRel (conflictGraph G).Adj]
    (ht : CliqueThresholds20 (conflictGraph G)) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card := by
  simpa only [conflictGraph_independent_iff] using
    subset_packing20_of_thresholds (conflictGraph G) ht F

end Se20Part.Legacy
