import Se20Insertion.Definitions

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

theorem sameComponent_refl (φ : PartialColouring H F) {a b : Colour} {x : W}
    (hx : x ∈ φ.Bicoloured a b) : φ.SameComponent a b x x :=
  ⟨hx, hx, .rfl⟩

theorem SameComponent.symm {φ : PartialColouring H F} {a b : Colour} {x y : W}
    (h : φ.SameComponent a b x y) : φ.SameComponent a b y x := by
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hy, hx, h.symm⟩

theorem SameComponent.trans {φ : PartialColouring H F} {a b : Colour} {x y z : W}
    (h : φ.SameComponent a b x y) (h' : φ.SameComponent a b y z) :
    φ.SameComponent a b x z := by
  obtain ⟨hx, hy, h⟩ := h
  obtain ⟨hy', hz, h'⟩ := h'
  exact ⟨hx, hz, h.trans h'⟩

theorem sameComponent_of_adj (φ : PartialColouring H F) {a b : Colour} {x y : W}
    (hx : x ∈ φ.Bicoloured a b) (hy : y ∈ φ.Bicoloured a b) (h : H.Adj x y) :
    φ.SameComponent a b x y := ⟨hx, hy, SimpleGraph.Adj.reachable h⟩

theorem component_closed (φ : PartialColouring H F) (a b : Colour) (x : W) :
    φ.KempeClosed a b {y | φ.SameComponent a b x y} := by
  refine ⟨fun y h => h.choose_spec.choose, ?_⟩
  intro y z hy hz hyz
  exact hy.trans (φ.sameComponent_of_adj hy.choose_spec.choose hz hyz)

theorem swapColour_eq_self (φ : PartialColouring H F) {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) {x : W}
    (ha : φ.colour x ≠ a) (hb : φ.colour x ≠ b) :
    φ.swapColour a b S x = φ.colour x := by
  have hx : x ∉ S := fun hx => (hS.1 hx).2.elim ha hb
  simp [swapColour, hx]

theorem swapColour_eq_iff (φ : PartialColouring H F) {a b c : Colour} {S : Set W}
    (ha : c ≠ a) (hb : c ≠ b) (x : W) :
    φ.swapColour a b S x = c ↔ φ.colour x = c := by
  simp only [swapColour]
  split
  · rw [Equiv.swap_apply_eq_iff]
    simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  · rfl

/-- Swap any union of whole components, preserving properness on exactly `F`. -/
def swap (φ : PartialColouring H F) (a b : Colour) (S : Set W)
    (hS : φ.KempeClosed a b S) : PartialColouring H F where
  colour := φ.swapColour a b S
  proper := by
    intro x y hx hy hxy heq
    by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S
    · exact φ.proper hx hy hxy ((Equiv.swap a b).injective (by simpa [swapColour, hxs, hys] using heq))
    · have hc : φ.colour y = a ∨ φ.colour y = b := by
        rcases (hS.1 hxs).2 with hxa | hxb
        · right; simpa [swapColour, hxs, hys, hxa] using heq.symm
        · left; simpa [swapColour, hxs, hys, hxb] using heq.symm
      exact hys (hS.2 hxs ⟨hy, hc⟩ hxy)
    · have hc : φ.colour x = a ∨ φ.colour x = b := by
        rcases (hS.1 hys).2 with hya | hyb
        · right; simpa [swapColour, hxs, hys, hya] using heq
        · left; simpa [swapColour, hxs, hys, hyb] using heq
      exact hxs (hS.2 hys ⟨hx, hc⟩ hxy.symm)
    · exact φ.proper hx hy hxy (by simpa [swapColour, hxs, hys] using heq)

/-- Union of the components containing an `a`-neighbour of some member of `B`. -/
def touching (φ : PartialColouring H F) (B : Set W) (a b : Colour) : Set W :=
  {y | ∃ f ∈ B, ∃ x, φ.Neighbour f a x ∧ φ.SameComponent a b x y}

theorem touching_closed (φ : PartialColouring H F) (B : Set W) (a b : Colour) :
    φ.KempeClosed a b (φ.touching B a b) := by
  constructor
  · rintro y ⟨f, hf, x, hx, hxy⟩
    exact hxy.choose_spec.choose
  · rintro y z ⟨f, hf, x, hx, hxy⟩ hz hyz
    exact ⟨f, hf, x, hx, hxy.trans (φ.sameComponent_of_adj hxy.choose_spec.choose hz hyz)⟩

/-- Joint separability frees `a` simultaneously at every member of `B`. -/
theorem jointSeparable_frees (φ : PartialColouring H F) {B : Set W} {a b : Colour}
    (hab : a ≠ b) (hsep : φ.JointSeparable B a b) :
    ∀ f ∈ B, (φ.swap a b (φ.touching B a b) (φ.touching_closed B a b)).Free f a := by
  intro f hf
  rintro ⟨y, hy, hfy, hcol⟩
  change φ.swapColour a b (φ.touching B a b) y = a at hcol
  by_cases hys : y ∈ φ.touching B a b
  · have hyb : φ.colour y = b := by
      simpa [swapColour, hys, Equiv.swap_apply_eq_iff] using hcol
    obtain ⟨g, hg, x, hx, hxy⟩ := hys
    exact hsep g hg f hf x y hx ⟨hy, hfy, hyb⟩ hxy
  · have hya : φ.colour y = a := by simpa [swapColour, hys] using hcol
    exact hys ⟨f, hf, y, ⟨hy, hfy, hya⟩, φ.sameComponent_refl ⟨hy, Or.inl hya⟩⟩

theorem separable_frees (φ : PartialColouring H F) {e : W} {a b : Colour}
    (hab : a ≠ b) (hsep : φ.Separable e a b) :
    ∃ ψ : PartialColouring H F, ψ.Free e a := by
  refine ⟨φ.swap a b (φ.touching {e} a b) (φ.touching_closed {e} a b), ?_⟩
  apply φ.jointSeparable_frees hab _ e (Set.mem_singleton e)
  simpa [JointSeparable, Separable] using hsep

/-- Insert a vertex with a free colour; in applications vertices are edges of `G`. -/
def insertFree [DecidableEq W] (φ : PartialColouring H F) (e : W) (a : Colour)
    (hfree : φ.Free e a) : PartialColouring H (insert e F) where
  colour x := if x = e then a else φ.colour x
  proper := by
    intro x y hx hy hxy heq
    by_cases hxe : x = e
    · subst x
      have hye : y ≠ e := hxy.ne.symm
      have hyF : y ∈ F := (Finset.mem_insert.mp hy).resolve_left hye
      exact hfree ⟨y, hyF, hxy, by simpa [hye] using heq.symm⟩
    · have hxF : x ∈ F := (Finset.mem_insert.mp hx).resolve_left hxe
      by_cases hye : y = e
      · subst y
        exact hfree ⟨x, hxF, hxy.symm, by simpa [hxe] using heq⟩
      · have hyF : y ∈ F := (Finset.mem_insert.mp hy).resolve_left hye
        exact φ.proper hxF hyF hxy (by simpa [hxe, hye] using heq)

theorem insert_of_separable [DecidableEq W] (φ : PartialColouring H F) {e : W}
    {a b : Colour} (hab : a ≠ b) (hsep : φ.Separable e a b) :
    Nonempty (PartialColouring H (insert e F)) := by
  obtain ⟨ψ, hψ⟩ := φ.separable_frees hab hsep
  exact ⟨ψ.insertFree e a hψ⟩

end PartialColouring
end Se20Insertion
