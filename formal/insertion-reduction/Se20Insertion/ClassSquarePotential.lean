import Se20Insertion.HoleStateEquivalence
import Se20Insertion.Fragmentation

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def classSize (φ : PartialColouring H F) (a : Colour) : ℤ :=
  (F.filter (φ.colour · = a)).card

def classSquare (φ : PartialColouring H F) : ℤ := ∑ a : Colour, φ.classSize a ^ 2

def imbalance (φ : PartialColouring H F) (a b : Colour) (S : Set W) : ℤ :=
  ((F.filter (fun x => x ∈ S ∧ φ.colour x = a)).card : ℤ) -
    (F.filter (fun x => x ∈ S ∧ φ.colour x = b)).card

theorem classSize_swap_left (φ : PartialColouring H F) {a b : Colour}
    (hab : a ≠ b) {S : Set W} (hS : φ.KempeClosed a b S) :
    (φ.swap a b S hS).classSize a = φ.classSize a - φ.imbalance a b S := by
  simp only [classSize, imbalance, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxS : x ∈ S <;> by_cases hxa : φ.colour x = a <;>
    by_cases hxb : φ.colour x = b <;>
    simp_all [swap, swapColour, Equiv.swap_apply_eq_iff, Ne.symm hab]

theorem classSize_swap_right (φ : PartialColouring H F) {a b : Colour}
    (hab : a ≠ b) {S : Set W} (hS : φ.KempeClosed a b S) :
    (φ.swap a b S hS).classSize b = φ.classSize b + φ.imbalance a b S := by
  have hS' : φ.KempeClosed b a S := by simpa [KempeClosed, Bicoloured, or_comm] using hS
  have hh := φ.classSize_swap_left hab.symm hS'
  have hh' : (φ.swap a b S hS).classSize b = φ.classSize b - φ.imbalance b a S := by
    simpa only [classSize, swap, swapColour, Equiv.swap_comm] using hh
  rw [hh']
  unfold imbalance
  ring

theorem classSize_swap_other (φ : PartialColouring H F) {a b c : Colour}
    (ha : c ≠ a) (hb : c ≠ b) {S : Set W} (hS : φ.KempeClosed a b S) :
    (φ.swap a b S hS).classSize c = φ.classSize c := by
  simp only [classSize, swap, φ.swapColour_eq_iff ha hb]

/-- The exact integer gain; d is signed, not natural subtraction. -/
theorem classSquare_swap (φ : PartialColouring H F) {a b : Colour}
    (hab : a ≠ b) {S : Set W} (hS : φ.KempeClosed a b S) :
    (φ.swap a b S hS).classSquare - φ.classSquare =
      2 * φ.imbalance a b S * (φ.imbalance a b S - (φ.classSize a - φ.classSize b)) := by
  have hs : (φ.swap a b S hS).classSquare - φ.classSquare =
      ((φ.swap a b S hS).classSize a ^ 2 - φ.classSize a ^ 2) +
      ((φ.swap a b S hS).classSize b ^ 2 - φ.classSize b ^ 2) := by
    rw [classSquare, classSquare, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ c ∈ ({a,b} : Finset Colour),
          ((φ.swap a b S hS).classSize c ^ 2 - φ.classSize c ^ 2) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro c _ hc
        have hn : c ≠ a ∧ c ≠ b := by simpa using hc
        rw [φ.classSize_swap_other hn.1 hn.2 hS, sub_self]
      _ = _ := by simp [hab]; ring
  rw [hs, φ.classSize_swap_left hab hS, φ.classSize_swap_right hab hS]
  ring

/-- P7 needs only local maximality for the specified component swap. -/
theorem propositionP7 (φ : PartialColouring H F) {a b : Colour}
    (hab : a ≠ b) {S : Set W} (hS : φ.KempeClosed a b S)
    (hmax : (φ.swap a b S hS).classSquare ≤ φ.classSquare)
    (hsize : φ.classSize b ≤ φ.classSize a) :
    0 ≤ φ.imbalance a b S ∧ φ.imbalance a b S ≤ φ.classSize a - φ.classSize b := by
  have hg := φ.classSquare_swap hab hS
  have hp : φ.imbalance a b S * (φ.imbalance a b S - (φ.classSize a - φ.classSize b)) ≤ 0 := by nlinarith [hg]
  constructor
  · by_contra hn
    have h1 : φ.imbalance a b S < 0 := by omega
    have h2 : φ.imbalance a b S - (φ.classSize a - φ.classSize b) < 0 := by omega
    exact (not_lt_of_ge hp) (mul_pos_of_neg_of_neg h1 h2)
  · by_contra hn
    have h1 : 0 < φ.imbalance a b S := by omega
    have h2 : 0 < φ.imbalance a b S - (φ.classSize a - φ.classSize b) := by omega
    exact (not_lt_of_ge hp) (mul_pos h1 h2)

theorem equal_classes_balanced (φ : PartialColouring H F) {a b : Colour}
    (hab : a ≠ b) {S : Set W} (hS : φ.KempeClosed a b S)
    (hmax : (φ.swap a b S hS).classSquare ≤ φ.classSquare)
    (hsize : φ.classSize a = φ.classSize b) : φ.imbalance a b S = 0 := by
  have hh := φ.propositionP7 hab hS hmax hsize.ge
  omega

theorem holeMove_classSquare [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) :
    (φ.holeMove hs).classSquare = φ.classSquare := by
  unfold classSquare classSize
  simp only [φ.holeMove_class_card he hs]

end Se20Insertion.PartialColouring
