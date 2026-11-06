import Se20Part.TransferCertificate

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000

def transferOrbit (M : Matrix (Fin 42) (Fin 42) ℚ) : ℕ → Fin 42 → ℚ
  | 0 => fun _ => 1
  | k+1 => M.mulVec (transferOrbit M k)

theorem transferOrbit_eq (M : Matrix (Fin 42) (Fin 42) ℚ) (k : ℕ) :
    transferOrbit M k = (M^k).mulVec (fun _ => 1) := by
  induction k with
  | zero => simp [transferOrbit]
  | succ k ih => rw [transferOrbit,ih,Matrix.mulVec_mulVec,← pow_succ']

theorem transferMass_eq_sum_orbit (M : Matrix (Fin 42) (Fin 42) ℚ) (k : ℕ) :
    transferMass M k = ∑ i, transferOrbit M k i := by
  simp [transferMass,transferOrbit_eq,Matrix.mulVec,dotProduct]

theorem exp31_mulVec_mono {x y : Fin 42 → ℚ} (h : ∀ i, x i ≤ y i) :
    ∀ i, exp31Matrix5710.mulVec x i ≤ exp31Matrix5710.mulVec y i := by
  intro i
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (h j)
    (exp31Matrix_nonneg (by norm_num [t5710,beta5710]) i j)

theorem exp31_orbit_nonneg (k : ℕ) : ∀ i, 0 ≤ transferOrbit exp31Matrix5710 k i := by
  induction k with
  | zero => intro i; norm_num [transferOrbit]
  | succ k ih =>
    intro i
    simp only [transferOrbit,Matrix.mulVec,dotProduct]
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (exp31Matrix_nonneg (by norm_num [t5710,beta5710]) i j) (ih j)

theorem exp31_transient_bound (k : ℕ) (hk : k ≤ 6) :
    ∀ i, transferOrbit exp31Matrix5710 k i ≤ certificateTransient ⟨k,by omega⟩ i / 1000000 := by
  induction k with
  | zero =>
    intro i
    have h := congrFun certificateTransient_start i
    simp only [transferOrbit]
    change 1 ≤ certificateTransient 0 i / 1000000
    rw [h]; norm_num
  | succ k ih =>
    have hb := ih (by omega)
    intro i
    have hm := exp31_mulVec_mono hb i
    have hc := certificateTransient_step ⟨k,by omega⟩ i
    rw [certificateStep_eq] at hc
    have he : exp31Matrix5710.mulVec
        (fun j => certificateTransient ⟨k,by omega⟩ j / 1000000) i =
        exp31Matrix5710.mulVec (certificateTransient ⟨k,by omega⟩) i / 1000000 := by
      simp [Matrix.mulVec,dotProduct,Finset.sum_div,mul_div_assoc]
    rw [he] at hm
    change 5710000 * exp31Matrix5710.mulVec (certificateTransient ⟨k,by omega⟩) i ≤
      5710000 * certificateTransient ⟨k+1,by omega⟩ i at hc
    change _ ≤ certificateTransient ⟨k+1,by omega⟩ i / 1000000
    dsimp only [transferOrbit]
    linarith

theorem exp31_tail_bound (k : ℕ) (hk : 6 ≤ k) :
    ∀ i, transferOrbit exp31Matrix5710 k i ≤
      certificateRho^k * certificateVector i / 1000000 := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro i
    have h := exp31_transient_bound 6 (by omega) i
    change transferOrbit exp31Matrix5710 6 i ≤ certificateTransient 6 i / 1000000 at h
    have he := certificateTransient_end i
    linarith
  | succ k hk ih =>
    intro i
    have hm := exp31_mulVec_mono ih i
    have hc := certificateVector_contract i
    rw [certificateStep_eq] at hc
    have hr : 0 ≤ certificateRho^k := pow_nonneg (by norm_num [certificateRho]) _
    have hc' : exp31Matrix5710.mulVec certificateVector i ≤ certificateRho * certificateVector i := by
      linarith
    have he : exp31Matrix5710.mulVec
        (fun j => certificateRho^k * certificateVector j / 1000000) i =
        certificateRho^k * exp31Matrix5710.mulVec certificateVector i / 1000000 := by
      simp only [Matrix.mulVec,dotProduct,Finset.sum_div,Finset.mul_sum]
      congr 1
      funext j
      ring
    rw [he] at hm
    have hh := mul_le_mul_of_nonneg_left hc' hr
    dsimp only [transferOrbit]
    rw [pow_succ]
    nlinarith

theorem exp31_mass_geometric (k : ℕ) :
    0 ≤ transferMass exp31Matrix5710 k ∧
      transferMass exp31Matrix5710 k ≤ 1200 * certificateRho^k := by
  rw [transferMass_eq_sum_orbit]
  refine ⟨Finset.sum_nonneg (fun i _ => exp31_orbit_nonneg k i),?_⟩
  by_cases hk : k ≤ 6
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => exp31_transient_bound k hk i)
    rw [← Finset.sum_div] at hs
    have hc := certificateTransient_sum ⟨k,by omega⟩
    dsimp only at hc
    linarith
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => exp31_tail_bound k (by omega) i)
    rw [← Finset.sum_div,← Finset.mul_sum] at hs
    have hr : 0 ≤ certificateRho^k := pow_nonneg (by norm_num [certificateRho]) _
    have hc := mul_le_mul_of_nonneg_left certificateVector_sum hr
    nlinarith

theorem exp31_convolution_bound :
    (∑ k ∈ Finset.range 2855, transferMass exp31Matrix5710 k *
      transferMass exp31Matrix5710 (2854-k)) ≤
      2855 * 1200^2 * certificateRho^2854 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range 2855, (1200^2 * certificateRho^2854) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ 2854 := by have := Finset.mem_range.mp hk; omega
      calc
        _ ≤ (1200 * certificateRho^k) * (1200 * certificateRho^(2854-k)) :=
          mul_le_mul (exp31_mass_geometric k).2 (exp31_mass_geometric _).2
            (exp31_mass_geometric _).1 (mul_nonneg (by norm_num) (pow_nonneg (by norm_num [certificateRho]) _))
        _ = _ := by rw [mul_mul_mul_comm,← pow_add,Nat.add_sub_of_le hk']; ring
    _ = _ := by simp; ring

theorem certificateRho_pow : certificateRho^2854 ≤ (753/10^20 : ℚ) := by
  norm_num [certificateRho]

theorem exp31_lllRhs_bound : lllRhs5710 exp31Matrix5710 ≤ (184410/1000000 : ℚ) := by
  have hc := exp31_convolution_bound
  have hp := certificateRho_pow
  have hs : (∑ k ∈ Finset.range 2855, transferMass exp31Matrix5710 k *
      transferMass exp31Matrix5710 (2854-k)) ≤ 2855 * 1200^2 * (753/10^20 : ℚ) := by
    nlinarith
  unfold lllRhs5710 transferContribution5710
  norm_num [t5710,beta5710,Finset.sum_Icc_succ_top]
  norm_num at hs
  linarith

theorem exp31_lll_budget : (lllRhs5710 exp31Matrix5710 : ℝ) < Real.log (1203/1000) := by
  have h : (lllRhs5710 exp31Matrix5710 : ℝ) ≤ (184410/1000000 : ℝ) := by
    have hh : (lllRhs5710 exp31Matrix5710 : ℝ) ≤ ((184410/1000000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr exp31_lllRhs_bound
    norm_num at hh ⊢
    exact hh
  linarith [log_beta5710_lower]

theorem exp31_certificate_slack :
    (184818/1000000 : ℚ) - 184410/1000000 = 51/125000 := by norm_num

end Se20Part
