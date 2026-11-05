import Se20Part.Definitions

noncomputable section
open scoped Classical
namespace Se20Part

/-- The five independent parts in the fixed 14-vertex graph of G15. -/
def petersenMinusPart (v : Fin 14) : ℕ :=
  if v.val < 4 then v.val else if v.val < 12 then (v.val-4)/2 else 4

def PetersenMinusConflict : SimpleGraph (Fin 14) where
  Adj x y := petersenMinusPart x ≠ petersenMinusPart y ∧
    ¬ ((x.val < 2 ∧ 2 ≤ y.val ∧ y.val < 4) ∨ (y.val < 2 ∧ 2 ≤ x.val ∧ x.val < 4))
  symm := ⟨by intros; aesop⟩
  loopless := ⟨by intro x; simp⟩

def petersenMinusListSize (v : Fin 14) : ℕ :=
  if v.val < 4 then 5 else if v.val < 12 then 7 else 8

/-- G15, explicitly a hypothesis, not an axiom or a proved instance.
The coefficient 12240 is not evaluated or trusted here. This is exactly its
arbitrary-list conclusion on the labelled graph in the supplied proof. -/
def PetersenMinusListTheoremG15 : Prop :=
  ∀ (ColourType : Type) (L : Fin 14 → Finset ColourType),
    (∀ v, petersenMinusListSize v ≤ (L v).card) →
    ∃ c : Fin 14 → ColourType, (∀ v, c v ∈ L v) ∧
      ∀ u v, PetersenMinusConflict.Adj u v → c u ≠ c v

theorem petersenMinus_degrees : ∀ v,
    PetersenMinusConflict.degree v = petersenMinusListSize v + 4 := by
  letI : DecidableRel PetersenMinusConflict.Adj := fun _ _ =>
    inferInstanceAs (Decidable (_ ∧ ¬ (_ ∨ _)))
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card,
    ← Fintype.card_eq_nat_card,SimpleGraph.card_neighborSet_eq_degree]
  have hh : ∀ v, PetersenMinusConflict.degree v = petersenMinusListSize v + 4 := by decide +kernel
  exact hh v

theorem petersenMinus_seventyFour_edges : Fintype.card PetersenMinusConflict.edgeSet = 74 := by
  rw [Fintype.card_eq_nat_card]
  letI : DecidableRel PetersenMinusConflict.Adj := fun _ _ =>
    inferInstanceAs (Decidable (_ ∧ ¬ (_ ∨ _)))
  rw [← Fintype.card_eq_nat_card,SimpleGraph.card_edgeSet]
  decide +kernel

end Se20Part
