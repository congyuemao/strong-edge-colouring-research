import Se20Part.Kempe

noncomputable section
open scoped Classical
namespace Se20Part
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


end PartialColouring
end Se20Part
