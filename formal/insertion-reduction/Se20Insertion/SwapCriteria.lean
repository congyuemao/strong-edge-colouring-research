import Se20Insertion.LowDegree

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

theorem swap_free_left_iff (φ : PartialColouring H F) {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) (v : W) :
    (φ.swap a b S hS).Free v a ↔
      (∀ x, φ.Neighbour v a x → x ∈ S) ∧ (∀ x, φ.Neighbour v b x → x ∉ S) := by
  constructor
  · intro hf
    constructor
    · intro x hx
      by_contra hxS
      exact hf ⟨x, hx.1, hx.2.1, by simp [swap, swapColour, hxS, hx.2.2]⟩
    · intro x hx hxS
      exact hf ⟨x, hx.1, hx.2.1, by simp [swap, swapColour, hxS, hx.2.2]⟩
  · rintro ⟨ha,hb⟩ ⟨x,hx,hvx,hc⟩
    change φ.swapColour a b S x = a at hc
    by_cases hxS : x ∈ S
    · have hxb : φ.colour x = b := by simpa [swapColour,hxS,Equiv.swap_apply_eq_iff] using hc
      exact hb x ⟨hx,hvx,hxb⟩ hxS
    · have hxa : φ.colour x = a := by simpa [swapColour,hxS] using hc
      exact hxS (ha x ⟨hx,hvx,hxa⟩)

theorem swap_free_right_iff (φ : PartialColouring H F) {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) (v : W) :
    (φ.swap a b S hS).Free v b ↔
      (∀ x, φ.Neighbour v b x → x ∈ S) ∧ (∀ x, φ.Neighbour v a x → x ∉ S) := by
  have hS' : φ.KempeClosed b a S := by
    simpa only [KempeClosed, Bicoloured, or_comm] using hS
  simpa only [Free, Neighbour, swap, swapColour, Equiv.swap_comm] using
    φ.swap_free_left_iff hS' v

/-- Lemma 11.28, an iff, valid even for a union of whole components. -/
theorem swap_unblocks_iff (φ : PartialColouring H F) {v : W}
    (hb : ∀ c, ∃ x, φ.Neighbour v c x) {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) :
    (∃ c, (φ.swap a b S hS).Free v c) ↔
      ((∀ x, φ.Neighbour v a x → x ∈ S) ∧ (∀ x, φ.Neighbour v b x → x ∉ S)) ∨
      ((∀ x, φ.Neighbour v b x → x ∈ S) ∧ (∀ x, φ.Neighbour v a x → x ∉ S)) := by
  constructor
  · rintro ⟨c,hc⟩
    by_cases hca : c = a
    · subst c; exact Or.inl ((φ.swap_free_left_iff hS v).mp hc)
    by_cases hcb : c = b
    · subst c; exact Or.inr ((φ.swap_free_right_iff hS v).mp hc)
    obtain ⟨x,hx⟩ := hb c
    exact False.elim (hc ⟨x,hx.1,hx.2.1,(φ.swapColour_eq_iff hca hcb x).mpr hx.2.2⟩)
  · rintro (h | h)
    · exact ⟨a,(φ.swap_free_left_iff hS v).mpr h⟩
    · exact ⟨b,(φ.swap_free_right_iff hS v).mpr h⟩

theorem separable_of_swap_unblocks (φ : PartialColouring H F) {v : W}
    (hb : ∀ c, ∃ x, φ.Neighbour v c x) {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) (hf : ∃ c, (φ.swap a b S hS).Free v c) :
    φ.Separable v a b := by
  rcases (φ.swap_unblocks_iff hb hS).mp hf with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · intro x y hx hy hxy
    exact hb y hy (hS.component_mem (ha x hx) hxy)
  · intro x y hx hy hxy
    exact ha x hx (hS.component_mem (hb y hy) hxy.symm)

/-- Exact list update in 11.24(2). The all/none/mixed cases follow by evaluating
the two predicates. Since eta is outside the old list, its neighbour set is nonempty. -/
theorem swap_two_list (φ : PartialColouring H F) (v : W) {γ δ η : Colour}
    (hγδ : γ ≠ δ) (hηγ : η ≠ γ) (hηδ : η ≠ δ)
    (hlist : φ.available v = {γ,δ}) {S : Set W} (hS : φ.KempeClosed γ η S)
    (c : Colour) :
    c ∈ (φ.swap γ η S hS).available v ↔
      c = δ ∨ (c = γ ∧ ∀ x, φ.Neighbour v η x → x ∉ S) ∨
        (c = η ∧ ∀ x, φ.Neighbour v η x → x ∈ S) := by
  have hγ : φ.Free v γ := (Finset.mem_filter.mp
    (show γ ∈ φ.available v by rw [hlist]; simp)).2
  have hfree (x : W) (hx : φ.Neighbour v γ x) : False := hγ ⟨x,hx⟩
  by_cases hcγ : c = γ
  · subst c
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and,
      φ.swap_free_left_iff hS v, hγδ, false_or, true_and, hηγ.symm, false_and, or_false]
    exact and_iff_right (fun x hx => (hfree x hx).elim)
  by_cases hcη : c = η
  · subst c
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and,
      φ.swap_free_right_iff hS v, hηδ, hηγ, false_or, false_and]
    exact and_iff_left (fun x hx => (hfree x hx).elim)
  have heq : (φ.swap γ η S hS).Free v c ↔ φ.Free v c := by
    unfold Free Neighbour
    simp only [swap, φ.swapColour_eq_iff hcγ hcη]
  have hmem : c ∈ φ.available v ↔ c = δ := by simp [hlist,hcγ]
  have hmem' : φ.Free v c ↔ c = δ := by simpa [available] using hmem
  simpa only [available, Finset.mem_filter, Finset.mem_univ, true_and,
    hcγ, hcη, false_and, or_false] using heq.trans hmem'

end Se20Insertion.PartialColouring
