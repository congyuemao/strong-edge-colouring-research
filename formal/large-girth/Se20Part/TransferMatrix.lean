import Se20Part.Numerics
import Se20Part.SpanningFamily

noncomputable section
open scoped Classical BigOperators
open SimpleGraph
namespace Se20Part

/-- The order in `exp31_lll_girth.py`: (1,1),...,(1,6),(1,99),...,(6,99). -/
def transferL (i : Fin 42) : ℕ := i.val / 7 + 1
def transferS (i : Fin 42) : ℕ := if i.val % 7 < 6 then i.val % 7 + 1 else 99

/-- Explicit rational matrix from the supplied program. Rows are destinations,
columns are sources, and transitions to the same state are added. -/
def exp31Matrix (t : ℚ) : Matrix (Fin 42) (Fin 42) ℚ := fun dst src =>
  let l := transferL src
  let s := transferS src
  let l₁ := min (l+1) 6
  let s₁ := min s (7-l) - 1
  if l ≤ 5 then
    (if 1 ≤ s₁ ∧ transferL dst = l₁ ∧ transferS dst = s₁ then 3 else 0) +
    ∑ d ∈ Finset.Icc 1 5,
      if 5 ≤ l₁+d then
        if d ≤ s₁ then
          if transferL dst = min l₁ d ∧ transferS dst = 99 then 6*3^d*t else 0
        else
          if 1 ≤ s₁ ∧ transferL dst = min l₁ d ∧ transferS dst = s₁ then 6*3^d*t else 0
      else 0
  else 0

def exp31Matrix5710 : Matrix (Fin 42) (Fin 42) ℚ := exp31Matrix t5710

theorem exp31Matrix_nonneg {t : ℚ} (ht : 0 ≤ t) (i j : Fin 42) : 0 ≤ exp31Matrix t i j := by
  dsimp only [exp31Matrix]
  split
  · apply add_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro d hd
      split_ifs <;> positivity
  · exact le_refl _

/-- A depth pattern on the n+1 positions of a segment; 0 denotes no selected edge. -/
abbrev SpanningPattern (n : ℕ) := Fin (n+1) → Fin 6

def ValidSpanningPattern {n : ℕ} (f : SpanningPattern n) : Prop :=
  (f 0).val ≠ 0 ∧
  (∀ i j, i < j → (f i).val ≠ 0 → (f j).val ≠ 0 →
    5 ≤ (f i).val+(f j).val+(j.val-i.val)) ∧
  ∀ k < n, ∃ i j, i.val ≤ k ∧ k < j.val ∧
    (f i).val ≠ 0 ∧ (f j).val ≠ 0 ∧ (f i).val+(f j).val+(j.val-i.val) ≤ 7

def spanningPatternWeight {n : ℕ} (t : ℚ) (f : SpanningPattern n) : ℚ :=
  3^n * ∏ i, if (f i).val = 0 then 1 else 2*3^((f i).val)*t

def spanningPatternCount (n : ℕ) (t : ℚ) : ℚ :=
  ∑ f : SpanningPattern n, if ValidSpanningPattern f then spanningPatternWeight t f else 0

def transferInitial (t : ℚ) (i : Fin 42) : ℚ :=
  if transferS i = 99 ∧ transferL i ≤ 5 then 2*3^(transferL i)*t else 0

def transferAcceptedCount (n : ℕ) (t : ℚ) : ℚ :=
  ∑ i, if transferS i = 99 then ∑ j, (exp31Matrix t ^ n) i j * transferInitial t j else 0

/-- The precise unproved correspondence, permitted as a named hypothesis in the
second-pass request. Short brute-force agreement is not a proof of this identity
for arbitrary segment lengths. This proposition is not an axiom. -/
def TransferMatrixSpanningCorrespondence : Prop :=
  ∀ n (t : ℚ), 0 ≤ t → transferAcceptedCount n t = spanningPatternCount n t

/-- The manuscript's rational numerical hypothesis now refers to a concrete matrix. -/
theorem exp31_numerical_suffices (h : TransferMatrix5710Bound exp31Matrix5710) :
    (lllRhs5710 exp31Matrix5710 : ℝ) < Real.log (1203/1000) :=
  numerical5710_suffices exp31Matrix5710 h

end Se20Part
