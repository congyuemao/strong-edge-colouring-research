import Se20Part.EvenPathExchange

noncomputable section
open scoped Classical
namespace Se20Part
variable {W : Type*} [Fintype W] (H J : SimpleGraph W)

/-- Moving a vertex out of a bad degree-two component creates at most one
replacement bad component. All other bad components inject into old ones. -/
theorem bad_count_le_of_old_bad (hΔ : ∀ v, H.degree v ≤ 2) (x : W)
    (heq : ∀ a b, a ≠ x → b ≠ x → (H.Adj a b ↔ J.Adj a b))
    (hold : ¬ (H.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    Fintype.card (BadComponent J) ≤ Fintype.card (BadComponent H) := by
  let f : BadComponent J → BadComponent H := fun K =>
    if hx : x ∈ K.val.supp then ⟨H.connectedComponentMk x, hold⟩
    else ⟨H.connectedComponentMk K.val.out,
      (bad_component_transfer H J hΔ x heq K hx).1⟩
  have fav (K : BadComponent J) (hx : x ∉ K.val.supp) : x ∉ (f K).val.supp := by
    simpa only [f, dif_neg hx] using (bad_component_transfer H J hΔ x heq K hx).2
  apply Fintype.card_le_of_injective f
  intro K L hKL
  have he : (f K).val = (f L).val := congrArg Subtype.val hKL
  by_cases hK : x ∈ K.val.supp
  · by_cases hL : x ∈ L.val.supp
    · apply Subtype.ext
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hK hL
    · apply False.elim
      apply fav L hL
      rw [← he]
      simp only [f,dif_pos hK]
      exact (H.connectedComponentMk x).mem_supp_iff x |>.mpr rfl
  · by_cases hL : x ∈ L.val.supp
    · apply False.elim
      apply fav K hK
      rw [he]
      simp only [f,dif_pos hL]
      exact (H.connectedComponentMk x).mem_supp_iff x |>.mpr rfl
    · let C := (f K).val
      have hmK : K.val.out ∈ C.supp := by
        simp only [C,f,dif_neg hK]
        exact (H.connectedComponentMk K.val.out).mem_supp_iff _ |>.mpr rfl
      have hmL : L.val.out ∈ C.supp := by
        change L.val.out ∈ (f K).val.supp
        rw [he]
        simp only [f,dif_neg hL]
        exact (H.connectedComponentMk L.val.out).mem_supp_iff _ |>.mpr rfl
      let g : C.toSimpleGraph →g J := {
        toFun := Subtype.val
        map_rel' := fun {a b} h => (heq a b (fun hh => fav K hK (hh ▸ a.prop))
          (fun hh => fav K hK (hh ▸ b.prop))).mp h }
      have hh := SimpleGraph.ConnectedComponent.sound
        (((C.connected_toSimpleGraph ⟨K.val.out,hmK⟩ ⟨L.val.out,hmL⟩).some.map g).reachable)
      apply Subtype.ext
      exact K.val.out_eq.symm.trans (hh.trans L.val.out_eq)

namespace Partition
variable {C : Type*} [Fintype C]

theorem minimumTwo_update_of_bad {π : W → C} (hπ : MinimumTwo H π)
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2) (x : W) (j : C)
    (hzero : degreeIn H π x j = degreeIn H π x (π x))
    (hodd : ¬ ((monochrome H π).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    MinimumTwo H (Function.update π x j) := by
  have hd : ∀ v, (monochrome H π).degree v ≤ 2 := by
    intro v
    have := hΔ v
    rw [← monochrome_degree] at this
    exact_mod_cast this
  have hc := bad_count_le_of_old_bad (monochrome H π)
    (monochrome H (Function.update π x j)) hd x
    (monochrome_update_off H π x j) hodd
  rw [← phi2_eq_card_bad, ← phi2_eq_card_bad] at hc
  exact ⟨minimum_update H hπ.1 x j hzero, fun σ hσ => hc.trans (hπ.2 σ hσ)⟩

/-- Triangles of a chosen geometric type, counted as unordered triples. -/
def typedTriangles (R : Finset W → Prop) (π : W → C) : Finset (Finset W) :=
  Finset.univ.filter (fun T => T.card = 3 ∧ R T ∧
    ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b ∧ π a = π b)

theorem mem_typedTriangles (R : Finset W → Prop) (π : W → C) (T : Finset W) :
    T ∈ typedTriangles H R π ↔ T.card = 3 ∧ R T ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → H.Adj a b ∧ π a = π b := by
  simp only [typedTriangles,Finset.mem_filter,Finset.mem_univ,true_and]

def MinimumThree (R : Finset W → Prop) (π : W → C) : Prop :=
  MinimumTwo H π ∧ ∀ σ : W → C, MinimumTwo H σ →
    (typedTriangles H R π).card ≤ (typedTriangles H R σ).card

theorem exists_minimumThree [Nonempty C] (R : Finset W → Prop) :
    ∃ π : W → C, MinimumThree H R π := by
  obtain ⟨π,hπ⟩ := exists_minimumTwo H (C := C)
  let A : Finset (W → C) := Finset.univ.filter (MinimumTwo H)
  obtain ⟨σ,hσ,hmin⟩ := A.exists_min_image (fun s => (typedTriangles H R s).card)
    ⟨π,by simp [A,hπ]⟩
  exact ⟨σ,(Finset.mem_filter.mp hσ).2,fun τ hτ => hmin τ (by simp [A,hτ])⟩

/-- A third-coordinate minimum replaces a destroyed typed triangle with
another through the moved vertex. The intermediate partition really is a
minimum of the first two coordinates. -/
theorem typed_triangle_replacement {R : Finset W → Prop} {π : W → C}
    (hπ : MinimumThree H R π) (x : W) (j : C) (hj : j ≠ π x)
    (hmin : MinimumTwo H (Function.update π x j))
    (T : Finset W) (hT : T ∈ typedTriangles H R π) (hx : x ∈ T) :
    ∃ S ∈ typedTriangles H R (Function.update π x j), x ∈ S := by
  by_contra! hn
  have hsub : typedTriangles H R (Function.update π x j) ⊆ typedTriangles H R π := by
    intro S hS
    obtain ⟨hs,hr,hcl⟩ := (Finset.mem_filter.mp hS).2
    have hav : ∀ a ∈ S, a ≠ x := fun a ha he => hn S hS (he ▸ ha)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hs,hr,?_⟩
    intro a ha b hb hab
    simpa only [Function.update_of_ne (hav a ha),Function.update_of_ne (hav b hb)]
      using hcl a ha b hb hab
  have hstrict : typedTriangles H R (Function.update π x j) ⊂ typedTriangles H R π :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hn T (he.symm ▸ hT) hx⟩
  have hh := Finset.card_lt_card hstrict
  have hl := hπ.2 _ hmin
  omega

end Partition
end Se20Part
