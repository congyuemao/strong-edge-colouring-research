import Se20Part.Definitions
import Mathlib.Data.Matrix.Basic

noncomputable section
open scoped BigOperators
namespace Se20Part

def beta5710 : ℚ := 1203 / 1000
def t5710 : ℚ := beta5710 / 5710

def transferMass (M : Matrix (Fin 42) (Fin 42) ℚ) (k : ℕ) : ℚ :=
  ∑ i, ∑ j, (M^k) i j

def transferContribution5710 (M : Matrix (Fin 42) (Fin 42) ℚ) : ℚ :=
  (9/4) * beta5710 * (∑ δ ∈ Finset.Icc 1 5, 12 * (3:ℚ)^δ) *
    ∑ k ∈ Finset.range 2855, transferMass M k * transferMass M (2854-k)

def lllRhs5710 (M : Matrix (Fin 42) (Fin 42) ℚ) : ℚ :=
  (1-t5710)⁻¹ * (726 * beta5710 * t5710 + transferContribution5710 M)

/-- Exact rational inequality printed in the manuscript, parameterized by a matrix.
The second-pass `TransferMatrix.lean` supplies `exp31Matrix5710` explicitly.
This is not a certificate for any particular matrix and is not an axiom. -/
def TransferMatrix5710Bound (M : Matrix (Fin 42) (Fin 42) ℚ) : Prop :=
  lllRhs5710 M ≤ 184154 / 1000000

theorem log_beta5710_lower : (184818/1000000 : ℝ) ≤ Real.log (1203/1000) := by
  have h := Real.sum_range_le_log_div (x := 203/2203) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The logarithmic comparison is proved; only the explicitly supplied matrix inequality remains. -/
theorem numerical5710_suffices (M : Matrix (Fin 42) (Fin 42) ℚ)
    (h : TransferMatrix5710Bound M) : (lllRhs5710 M : ℝ) < Real.log (1203/1000) := by
  have h' : (lllRhs5710 M : ℝ) ≤ (184154/1000000 : ℝ) := by
    have hc : (lllRhs5710 M : ℝ) ≤ ((184154/1000000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    norm_num at hc ⊢
    exact hc
  linarith [log_beta5710_lower]

theorem numerical5710_slack :
    (184818/1000000 : ℚ) - 184154/1000000 = 83/125000 := by norm_num

end Se20Part
