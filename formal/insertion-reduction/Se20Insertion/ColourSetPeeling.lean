import Se20Insertion.ColourSetCore

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Simultaneously remove every vertex whose current degree is below threshold. -/
def colourPeelStep (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (R : Finset W) : Finset W :=
  R.filter (fun v => φ.colourSetThreshold h Y v ≤ (domainNeighbours H R v).card)

def colourPeel (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : ℕ → Finset W
  | 0 => φ.colourSetS h Y
  | n + 1 => φ.colourPeelStep h Y (φ.colourPeel h Y n)

theorem core_subset_peelStep (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    {R : Finset W} (hr : φ.colourSetCore h Y ⊆ R) :
    φ.colourSetCore h Y ⊆ φ.colourPeelStep h Y R := by
  intro v hv
  refine Finset.mem_filter.mpr ⟨hr hv, ((φ.colourSetCore_isCore h Y).2 v hv).trans ?_⟩
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hr)

theorem colourPeel_invariants (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (n : ℕ) :
    φ.colourSetCore h Y ⊆ φ.colourPeel h Y n ∧ φ.colourPeel h Y n ⊆ φ.colourSetS h Y := by
  induction n with
  | zero => exact ⟨(φ.colourSetCore_isCore h Y).1, Finset.Subset.refl _⟩
  | succ n ih =>
    exact ⟨φ.core_subset_peelStep h Y ih.1, (Finset.filter_subset _ _).trans ih.2⟩

theorem colourPeelStep_core (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    φ.colourPeelStep h Y (φ.colourSetCore h Y) = φ.colourSetCore h Y :=
  Finset.Subset.antisymm (Finset.filter_subset _ _) (φ.core_subset_peelStep h Y (Finset.Subset.refl _))

theorem colourPeel_eq_core_of_stable (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    (n : ℕ) (hs : φ.colourPeel h Y (n + 1) = φ.colourPeel h Y n) :
    φ.colourPeel h Y n = φ.colourSetCore h Y := by
  apply Finset.Subset.antisymm _ (φ.colourPeel_invariants h Y n).1
  apply φ.colourSetCore_greatest
  refine ⟨(φ.colourPeel_invariants h Y n).2, ?_⟩
  intro v hv
  have : v ∈ φ.colourPeel h Y (n + 1) := hs.symm ▸ hv
  exact (Finset.mem_filter.mp this).2

/-- A finite simultaneous peeling procedure computes the same core. -/
theorem colourPeel_stabilizes (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    φ.colourPeel h Y ((φ.colourSetS h Y).card + 1) = φ.colourSetCore h Y := by
  have bound : ∀ n, φ.colourPeel h Y n = φ.colourSetCore h Y ∨
      (φ.colourPeel h Y n).card + n ≤ (φ.colourSetS h Y).card := by
    intro n
    induction n with
    | zero => exact Or.inr (by simp [colourPeel])
    | succ n ih =>
      rcases ih with heq | hb
      · left
        simpa only [colourPeel, heq] using φ.colourPeelStep_core h Y
      · by_cases heq : φ.colourPeel h Y (n + 1) = φ.colourPeel h Y n
        · exact Or.inl (heq.trans (φ.colourPeel_eq_core_of_stable h Y n heq))
        · right
          have hsub : φ.colourPeel h Y (n + 1) ⊆ φ.colourPeel h Y n := Finset.filter_subset _ _
          have hlt : (φ.colourPeel h Y (n + 1)).card < (φ.colourPeel h Y n).card := by
            apply Finset.card_lt_card
            exact (Finset.ssubset_iff_subset_ne).mpr ⟨hsub, heq⟩
          omega
  rcases bound ((φ.colourSetS h Y).card + 1) with heq | hb
  · exact heq
  · omega

theorem not_mem_core_iff_peeled (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    h ∉ φ.colourSetCore h Y ↔ h ∉ φ.colourPeel h Y ((φ.colourSetS h Y).card + 1) := by
  rw [φ.colourPeel_stabilizes]

end Se20Insertion.PartialColouring
