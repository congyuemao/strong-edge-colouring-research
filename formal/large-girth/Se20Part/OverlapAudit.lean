import Se20Part.Definitions

namespace Se20Part

/-- Two disjoint conflict edges. This graph has maximum degree one. -/
def overlapGraph : SimpleGraph (Fin 4) where
  Adj x y := (x=0 ∧ y=1) ∨ (x=1 ∧ y=0) ∨ (x=2 ∧ y=3) ∨ (x=3 ∧ y=2)
  symm := ⟨by intro x y h; tauto⟩
  loopless := ⟨by intro x h; rcases h with h | h | h | h <;> omega⟩

instance : DecidableRel overlapGraph.Adj := by
  intro x y
  change Decidable ((x=0 ∧ y=1) ∨ (x=1 ∧ y=0) ∨ (x=2 ∧ y=3) ∨ (x=3 ∧ y=2))
  infer_instance

def overlapParts : Fin 4 → Finset (Fin 4) := ![{0,2}, {0,3}, {1,2}, {1,3}]

theorem overlapParts_size : ∀ i, (overlapParts i).card = 2 := by decide

theorem overlapGraph_degree : ∀ v, overlapGraph.degree v = 1 := by decide

/- Haxell cannot be applied to arbitrary overlapping size-two lists, even in degree one. -/
set_option maxRecDepth 10000 in
theorem overlapping_transversal_false :
    ¬ ∃ f : Fin 4 → Fin 4, (∀ i, f i ∈ overlapParts i) ∧
      ∀ i j, i ≠ j → ¬ overlapGraph.Adj (f i) (f j) := by decide

end Se20Part
