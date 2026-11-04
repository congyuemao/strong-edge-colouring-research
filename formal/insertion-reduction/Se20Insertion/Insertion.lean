import Se20Insertion.Kempe

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Simultaneously recolour an independent set whose target colour is free. -/
def recolour (φ : PartialColouring H F) (B : Set W) (a : Colour)
    (hind : ∀ x ∈ B, ∀ y ∈ B, ¬ H.Adj x y)
    (hfree : ∀ x ∈ B, φ.Free x a) : PartialColouring H F where
  colour x := if x ∈ B then a else φ.colour x
  proper := by
    intro x y hx hy hxy heq
    by_cases hxb : x ∈ B <;> by_cases hyb : y ∈ B
    · exact hind x hxb y hyb hxy
    · exact hfree x hxb ⟨y, hy, hxy, by simpa [hxb, hyb] using heq.symm⟩
    · exact hfree y hyb ⟨x, hx, hxy.symm, by simpa [hxb, hyb] using heq⟩
    · exact φ.proper hx hy hxy (by simpa [hxb, hyb] using heq)

/-- Theorem 11.14: insertion through an entire colour class of neighbours. -/
theorem colourClassInsertion [DecidableEq W] (φ : PartialColouring H F) (e : W)
    {c a b : Colour} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsep : φ.JointSeparable {g | φ.Neighbour e c g} a b) :
    Nonempty (PartialColouring H (insert e F)) := by
  let B : Set W := {g | φ.Neighbour e c g}
  let ψ := φ.swap a b (φ.touching B a b) (φ.touching_closed B a b)
  have hind : ∀ x ∈ B, ∀ y ∈ B, ¬ H.Adj x y := by
    intro x hx y hy hxy
    exact φ.proper hx.1 hy.1 hxy (hx.2.2.trans hy.2.2.symm)
  have hfree : ∀ x ∈ B, ψ.Free x a := φ.jointSeparable_frees hab hsep
  let θ := ψ.recolour B a hind hfree
  have he : θ.Free e c := by
    rintro ⟨g, hg, heg, hc⟩
    change (if g ∈ B then a else ψ.colour g) = c at hc
    by_cases hgb : g ∈ B
    · exact hac (by simpa [hgb] using hc)
    · have hcψ : ψ.colour g = c := by simpa [hgb] using hc
      have hcφ : φ.colour g = c :=
        (φ.swapColour_eq_iff hac.symm hbc.symm g).mp hcψ
      exact hgb ⟨hg, heg, hcφ⟩
  exact ⟨θ.insertFree e c he⟩

/-- Theorem 11.7, the length-one chain needed by Conjecture 11.9. -/
theorem singleInsertion [DecidableEq W] (φ : PartialColouring H F) {e f : W}
    {p a b : Colour} (hs : φ.Single e p f)
    (hab : a ≠ b) (hap : a ≠ p) (hbp : b ≠ p) (hsep : φ.Separable f a b) :
    Nonempty (PartialColouring H (insert e F)) := by
  apply φ.colourClassInsertion e hab hap hbp
  intro x hx y hy
  have hx' : x = f := hs.2 x hx
  have hy' : y = f := hs.2 y hy
  subst x; subst y
  exact hsep

theorem repairableInsertion [DecidableEq W] (φ : PartialColouring H F) {e : W}
    (h : φ.Repairable e) : Nonempty (PartialColouring H (insert e F)) := by
  rcases h with ⟨a, ha⟩ | ⟨a, b, hab, hsep⟩ | ⟨p, f, hs, a, b, hab, hap, hbp, hsep⟩
  · exact ⟨φ.insertFree e a ha⟩
  · exact φ.insert_of_separable hab hsep
  · exact φ.singleInsertion hs hab hap hbp hsep

theorem free_or_separable_or_stuck (φ : PartialColouring H F) (e : W) :
    (∃ a, φ.Free e a) ∨ (∃ a b, a ≠ b ∧ φ.Separable e a b) ∨ φ.Stuck e := by
  by_cases hf : ∃ a, φ.Free e a
  · exact Or.inl hf
  right
  by_cases hs : ∃ a b, a ≠ b ∧ φ.Separable e a b
  · exact Or.inl hs
  right
  constructor
  · simpa [Free, not_exists, not_not] using hf
  · intro a b hab hsep
    exact hs ⟨a, b, hab, hsep⟩

/-- Induction is on subsets of a fixed graph, never on edge-deleted graphs. -/
theorem colourable_of_insertion [Fintype W] [DecidableEq W]
    (hi : ∀ (F : Finset W) (φ : PartialColouring H F) (e : W), e ∉ F →
      Nonempty (PartialColouring H (insert e F))) : H.Colorable 20 := by
  have all : ∀ F : Finset W, Nonempty (PartialColouring H F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨⟨fun _ => 0, by simp⟩⟩
    | @insert e F he ih =>
      obtain ⟨φ⟩ := ih
      exact hi F φ e he
  obtain ⟨φ⟩ := all Finset.univ
  exact ⟨SimpleGraph.Coloring.mk φ.colour (φ.proper (Finset.mem_univ _) (Finset.mem_univ _))⟩

end PartialColouring

theorem conj119Star_of_conj119 : Conj119 → Conj119Star := by
  intro h n G hreg v hv U hU htri φ
  obtain ⟨e, he⟩ := hU.1
  refine ⟨e, he, ?_⟩
  rcases φ.free_or_separable_or_stuck e with hf | hs | hstuck
  · exact Or.inl hf
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (h n G (fun v => (hreg v).le) _ φ e (by simp [he]) hstuck))

theorem starInsertion_of_conj119Star (h : Conj119Star) : StarInsertion := by
  intro n G hreg v hv U hU htri φ
  obtain ⟨e, he, hrepair⟩ := h n G hreg v hv U hU htri φ
  exact ⟨e, he, φ.repairableInsertion hrepair⟩

theorem strongColourable_fin_of_conj119 (h : Conj119) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hΔ : MaxDegreeFour G) : StrongColourable G 20 := by
  apply PartialColouring.colourable_of_insertion
  intro F φ e he
  apply φ.repairableInsertion
  rcases φ.free_or_separable_or_stuck e with hf | hs | hstuck
  · exact Or.inl hf
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (h n G hΔ F φ e he hstuck))

theorem strongColourable_fin_of_conj1115 (h : Conj1115) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hΔ : MaxDegreeFour G) : StrongColourable G 20 := by
  apply PartialColouring.colourable_of_insertion
  intro F φ e he
  rcases φ.free_or_separable_or_stuck e with ⟨a, ha⟩ | ⟨a, b, hab, hsep⟩ | hstuck
  · exact ⟨φ.insertFree e a ha⟩
  · exact φ.insert_of_separable hab hsep
  · obtain ⟨c, a, b, hab, hac, hbc, hsep⟩ := h n G hΔ F φ e he hstuck
    exact φ.colourClassInsertion e hab hac hbc hsep

end Se20Insertion
