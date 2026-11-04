import Se20Insertion.Insertion

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- A swap selected in the original colouring can be applied after swaps on
disjoint colour pairs. Only the two relevant colour fibres need agree. -/
theorem swap_original_frees (φ ψ : PartialColouring H F) (B : Set W) {a b : Colour}
    (hab : a ≠ b) (hsep : φ.JointSeparable B a b)
    (ha : ∀ x, ψ.colour x = a ↔ φ.colour x = a)
    (hb : ∀ x, ψ.colour x = b ↔ φ.colour x = b) :
    ∃ θ : PartialColouring H F,
      (∀ x ∈ B, θ.Free x a) ∧
      (∀ c, c ≠ a → c ≠ b → ∀ x, θ.colour x = c ↔ ψ.colour x = c) := by
  let S := φ.touching B a b
  have hB : ∀ x, x ∈ ψ.Bicoloured a b ↔ x ∈ φ.Bicoloured a b := by
    intro x
    exact and_congr Iff.rfl (or_congr (ha x) (hb x))
  have hclosed : ψ.KempeClosed a b S := by
    refine ⟨fun x hx => (hB x).mpr ((φ.touching_closed B a b).1 hx), ?_⟩
    intro x y hx hy hxy
    exact (φ.touching_closed B a b).2 hx ((hB y).mp hy) hxy
  let θ := ψ.swap a b S hclosed
  refine ⟨θ, ?_, fun c hca hcb x => ψ.swapColour_eq_iff hca hcb x⟩
  intro f hf
  rintro ⟨y, hy, hfy, hycol⟩
  change ψ.swapColour a b S y = a at hycol
  by_cases hyS : y ∈ S
  · have hyb : ψ.colour y = b := by
      simpa [swapColour, hyS, Equiv.swap_apply_eq_iff] using hycol
    obtain ⟨g, hg, x, hx, hxy⟩ := hyS
    exact hsep g hg f hf x y hx ⟨hy, hfy, (hb y).mp hyb⟩ hxy
  · have hya : φ.colour y = a := (ha y).mp (by simpa [swapColour, hyS] using hycol)
    exact hyS ⟨f, hf, y, ⟨hy, hfy, hya⟩, φ.sameComponent_refl ⟨hy, Or.inl hya⟩⟩

/-- Theorem 11.18. `B` may be any cover of the neighbour colour class; in
particular, a partition as in the manuscript satisfies these hypotheses. -/
theorem groupedColourClassInsertion [DecidableEq W] {I : Type*} [Fintype I]
    (φ : PartialColouring H F) (e : W) (c : Colour) (B : I → Set W) (a b : I → Colour)
    (hcover : ∀ x, φ.Neighbour e c x ↔ ∃ i, x ∈ B i)
    (hab : ∀ i, a i ≠ b i) (hac : ∀ i, a i ≠ c) (hbc : ∀ i, b i ≠ c)
    (hdisj : ∀ i j, i ≠ j →
      a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j)
    (hsep : ∀ i, φ.JointSeparable (B i) (a i) (b i)) :
    Nonempty (PartialColouring H (insert e F)) := by
  have swaps : ∀ S : Finset I, ∃ ψ : PartialColouring H F,
      (∀ i ∈ S, ∀ x ∈ B i, ψ.Free x (a i)) ∧
      (∀ r, (∀ i ∈ S, r ≠ a i ∧ r ≠ b i) → ∀ x, ψ.colour x = r ↔ φ.colour x = r) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨φ, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ψ, hfree, hout⟩ := ih
      have hai : ∀ x, ψ.colour x = a i ↔ φ.colour x = a i := hout (a i) (by
        intro j hj
        have hh := hdisj i j (fun h => hi (h ▸ hj))
        exact ⟨hh.1, hh.2.1⟩)
      have hbi : ∀ x, ψ.colour x = b i ↔ φ.colour x = b i := hout (b i) (by
        intro j hj
        have hh := hdisj i j (fun h => hi (h ▸ hj))
        exact ⟨hh.2.2.1, hh.2.2.2⟩)
      obtain ⟨θ, hθfree, hθout⟩ := swap_original_frees φ ψ (B i) (hab i) (hsep i) hai hbi
      refine ⟨θ, ?_, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with hji | hjS
        · subst j; exact hθfree x hx
        · have hji : j ≠ i := fun h => hi (h ▸ hjS)
          have hh := hdisj j i hji
          rintro ⟨y, hyF, hxy, hycol⟩
          exact hfree j hjS x hx ⟨y, hyF, hxy, (hθout (a j) hh.1 hh.2.1 y).mp hycol⟩
      · intro r hr x
        have hri := hr i (Finset.mem_insert_self _ _)
        exact (hθout r hri.1 hri.2 x).trans (hout r
          (fun j hj => hr j (Finset.mem_insert_of_mem hj)) x)
  obtain ⟨ψ, hfree, hout⟩ := swaps Finset.univ
  have hc : ∀ x, ψ.colour x = c ↔ φ.colour x = c := hout c
    (fun i _ => ⟨(hac i).symm, (hbc i).symm⟩)
  let C : Set W := {x | φ.Neighbour e c x}
  have hex : ∀ x ∈ C, ∃ i, x ∈ B i := fun x hx => (hcover x).mp hx
  let group (x : W) (hx : x ∈ C) : I := (hex x hx).choose
  have hgroup (x : W) (hx : x ∈ C) : x ∈ B (group x hx) := (hex x hx).choose_spec
  let colour (x : W) := if hx : x ∈ C then a (group x hx) else ψ.colour x
  have hind : ∀ x ∈ C, ∀ y ∈ C, ¬ H.Adj x y := by
    intro x hx y hy hxy
    exact φ.proper hx.1 hy.1 hxy (hx.2.2.trans hy.2.2.symm)
  have hproper : ∀ ⦃x y⦄, x ∈ F → y ∈ F → H.Adj x y → colour x ≠ colour y := by
    intro x y hxF hyF hxy hcol
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
    · exact hind x hx y hy hxy
    · exact hfree (group x hx) (Finset.mem_univ _) x (hgroup x hx)
        ⟨y, hyF, hxy, by simpa [colour, hx, hy] using hcol.symm⟩
    · exact hfree (group y hy) (Finset.mem_univ _) y (hgroup y hy)
        ⟨x, hxF, hxy.symm, by simpa [colour, hx, hy] using hcol⟩
    · exact ψ.proper hxF hyF hxy (by simpa [colour, hx, hy] using hcol)
  let θ : PartialColouring H F := ⟨colour, hproper⟩
  have hefree : θ.Free e c := by
    rintro ⟨x, hxF, hex, hxc⟩
    change colour x = c at hxc
    by_cases hx : x ∈ C
    · exact hac (group x hx) (by simpa [colour, hx] using hxc)
    · have hψ : ψ.colour x = c := by simpa [colour, hx] using hxc
      exact hx ⟨hxF, hex, (hc x).mp hψ⟩
  exact ⟨θ.insertFree e c hefree⟩

end PartialColouring
end Se20Insertion
