import Se20Part.FiniteEndBlock
import Se20Part.CriticalColourTools

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part

/-- A connected degree-list obstruction has a complete or odd-cycle end
block, with an explicit nonempty interior and at most one boundary vertex. -/
theorem bad_lists_end_block {W C : Type*} [Fintype W] [Nonempty C]
    (H : SimpleGraph W) (L : W → Finset C) (hc : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card)
    (hb : ¬ DegreeList.ColourableOn H L Finset.univ) :
    ∃ S B : Finset W, S.Nonempty ∧ S ⊆ B ∧ (B \ S).card ≤ 1 ∧
      (∀ x ∈ S, ∀ y, H.Adj x y → y ∈ B) ∧ BlockEligible H B ∧
      ((∀ x ∈ B, ∀ y ∈ B, x ≠ y → H.Adj x y) ∨
        DegreeList.IsOddCycleGraph (H.induce (B : Set W))) := by
  letI : Nonempty W := hc.nonempty
  obtain ⟨S,B,hs,hsb,hbs,hcl,he⟩ := exists_end_block H
  obtain ⟨L',hd',hb'⟩ := DegreeList.bad_induced_lists H L hc hd hb B (hs.mono hsb)
  exact ⟨S,B,hs,hsb,hbs,hcl,he,
    DegreeList.eligible_bad_lists_complete_or_odd H B he L' hd' hb'⟩

/-- The no-high-vertex branch of A02/A03/A04: a critical graph of maximum
degree k≥3 necessarily contains a (k+1)-clique. -/
theorem critical_regular_has_clique {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 3 ≤ k)
    (hmin : VertexMinimalNoncolourable H k) (hΔ : ∀ x, H.degree x ≤ k) :
    ∃ B : Finset W, B.card = k+1 ∧ H.IsClique (B : Set W) := by
  have hr : ∀ x, H.degree x = k := fun x =>
    Nat.le_antisymm (hΔ x) (vertex_minimal_noncolourable_degree H k hmin x)
  have hn : Nonempty W := by
    by_contra hn
    haveI : IsEmpty W := not_nonempty_iff.mp hn
    exact hmin.1 ⟨SimpleGraph.Coloring.mk isEmptyElim (fun {x} => isEmptyElim x)⟩
  letI : Nonempty W := hn
  obtain ⟨S,B,hs,hsb,_,hcl,he⟩ := exists_end_block H
  obtain ⟨x,hx⟩ := hs
  have hxB := hsb hx
  have hd : (H.induce (B : Set W)).degree ⟨x,hxB⟩ = k := by
    rw [degree_induce_finset]
    have heq : B.filter (H.Adj x) = H.neighborFinset x := by
      ext y
      simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset]
      exact ⟨And.right,fun hy => ⟨hcl x hx y hy,hy⟩⟩
    rw [heq,SimpleGraph.card_neighborFinset_eq_degree,hr]
  rcases minimal_low_block_classification H k hmin B he.1 he.2
      (fun v _ => hr v) with hb | ho
  · refine ⟨B,?_,fun u hu v hv huv => hb u hu v hv huv⟩
    have heq : B.filter (H.Adj x) = B.erase x := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_erase]
      exact ⟨fun h => ⟨h.2.ne.symm,h.1⟩,fun h => ⟨h.2,hb x hxB y h.2 h.1.symm⟩⟩
    rw [degree_induce_finset,heq] at hd
    have hh := Finset.card_erase_add_one hxB
    omega
  · have hh := ho.2.2 ⟨x,hxB⟩
    simp only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hd hh
    omega

/-- Brooks' k≥3 case, now obtained from the proved Gallai theorem and an
explicit end block. This does not change the older named Brooks interfaces. -/
theorem colourable_of_degree_le_no_clique {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 3 ≤ k)
    (hΔ : ∀ x, H.degree x ≤ k)
    (hcl : ∀ B : Finset W, H.IsClique (B : Set W) → B.card ≤ k) : H.Colorable k := by
  by_contra hn
  obtain ⟨A,hA⟩ := exists_vertex_minimal_noncolourable H k hn
  have hdeg : ∀ x : A, (H.induce (A : Set W)).degree x ≤ k := by
    intro x
    rw [degree_induce_finset]
    apply le_trans _ (hΔ x.val)
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hy).2
  obtain ⟨B,hB,hc⟩ := critical_regular_has_clique _ k hk hA hdeg
  have hc' : H.IsClique (↑(B.image Subtype.val) : Set W) := by
    intro u hu v hv huv
    change u ∈ B.image Subtype.val at hu
    change v ∈ B.image Subtype.val at hv
    obtain ⟨uu,huu,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨vv,hvv,rfl⟩ := Finset.mem_image.mp hv
    exact hc huu hvv (fun he => huv (congrArg Subtype.val he))
  have hh := hcl (B.image Subtype.val) hc'
  rw [Finset.card_image_of_injective _ Subtype.val_injective,hB] at hh
  omega

end Se20Part
