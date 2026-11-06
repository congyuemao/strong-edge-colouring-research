import Se20Part.TransferFineCertificate
import Se20Part.TransferEstimate

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option exponentiation.threshold 10000

theorem exp31_normalized_transient (k : ℕ) (hk : k ≤ 100) : ∀ i,
    transferOrbit exp31Matrix5710 k i ≤ fineRho^k * fineOrbit ⟨k,by omega⟩ i / fineScale := by
  induction k with
  | zero =>
    intro i
    change 1 ≤ fineRho^0 * fineOrbit 0 i / fineScale
    rw [fine_start]
    norm_num [fineScale]
  | succ k ih =>
    have hm := exp31_mulVec_mono (ih (by omega))
    intro i
    have hc := fine_step ⟨k,by omega⟩ i
    rw [certificateStep_eq] at hc
    change 10000000 * (5710000 * exp31Matrix5710.mulVec (fineOrbit ⟨k,by omega⟩) i) ≤
      (5710000*9862789) * fineOrbit ⟨k+1,by omega⟩ i at hc
    have hc' : exp31Matrix5710.mulVec (fineOrbit ⟨k,by omega⟩) i ≤
        fineRho * fineOrbit ⟨k+1,by omega⟩ i := by
      norm_num [fineRho]; linarith
    have he : exp31Matrix5710.mulVec (fun j => fineRho^k * fineOrbit ⟨k,by omega⟩ j / fineScale) i =
        fineRho^k * exp31Matrix5710.mulVec (fineOrbit ⟨k,by omega⟩) i / fineScale := by
      simp only [Matrix.mulVec,dotProduct,Finset.sum_div,Finset.mul_sum]
      congr 1
      funext j
      ring
    have hh := hm i
    rw [he] at hh
    have hr : 0 ≤ fineRho^k := pow_nonneg (by norm_num [fineRho]) _
    have hmul := mul_le_mul_of_nonneg_left hc' hr
    change _ ≤ fineRho^(k+1) * fineOrbit ⟨k+1,by omega⟩ i / fineScale
    rw [pow_succ]
    dsimp only [transferOrbit,fineScale] at *
    nlinarith

theorem exp31_normalized_tail (k : ℕ) (hk : 100 ≤ k) : ∀ i,
    transferOrbit exp31Matrix5710 k i ≤ fineRho^k * fineVector i / fineScale := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro i
    have h := exp31_normalized_transient 100 (by omega) i
    change transferOrbit exp31Matrix5710 100 i ≤ fineRho^100 * fineOrbit 100 i / fineScale at h
    have hr : 0 ≤ fineRho^100 := pow_nonneg (by norm_num [fineRho]) _
    have hh := mul_le_mul_of_nonneg_left (fine_end i) hr
    dsimp only [fineScale] at *
    linarith
  | succ k hk ih =>
    intro i
    have hm := exp31_mulVec_mono ih i
    have hc := fine_contract i
    rw [certificateStep_eq] at hc
    have hc' : exp31Matrix5710.mulVec fineVector i ≤ fineRho * fineVector i := by
      norm_num [fineRho]; linarith
    have he : exp31Matrix5710.mulVec (fun j => fineRho^k * fineVector j / fineScale) i =
        fineRho^k * exp31Matrix5710.mulVec fineVector i / fineScale := by
      simp only [Matrix.mulVec,dotProduct,Finset.sum_div,Finset.mul_sum]
      congr 1
      funext j
      ring
    rw [he] at hm
    have hh := mul_le_mul_of_nonneg_left hc' (pow_nonneg (by norm_num [fineRho] : 0 ≤ fineRho) k)
    dsimp only [transferOrbit,fineScale] at *
    rw [pow_succ]
    nlinarith

theorem fineEnvelope_nonneg (k : ℕ) : 0 ≤ fineEnvelope k := by
  unfold fineEnvelope
  split_ifs with h
  · exact fine_mass_nonneg ⟨k,h⟩
  · norm_num [fineConstant]

theorem exp31_fine_mass (k : ℕ) :
    transferMass exp31Matrix5710 k ≤ fineRho^k * fineEnvelope k / fineScale := by
  rw [transferMass_eq_sum_orbit]
  by_cases hk : k < 100
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => exp31_normalized_transient k (by omega) i)
    rw [← Finset.sum_div,← Finset.mul_sum] at hs
    have hc := fine_mass_sum ⟨k,hk⟩
    change (∑ i, fineOrbit ⟨k,by omega⟩ i) ≤ fineMasses ⟨k,hk⟩ at hc
    have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num [fineRho] : 0 ≤ fineRho) k)
    simp only [fineEnvelope,dif_pos hk,fineScale] at *
    linarith
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => exp31_normalized_tail k (by omega) i)
    rw [← Finset.sum_div,← Finset.mul_sum] at hs
    have hh := mul_le_mul_of_nonneg_left fine_vector_sum (pow_nonneg (by norm_num [fineRho] : 0 ≤ fineRho) k)
    simp only [fineEnvelope,dif_neg hk,fineScale] at *
    linarith

theorem exp31_fine_convolution :
    (∑ k ∈ Finset.range 2855, transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k)) ≤
      fineRho^2854 / fineScale^2 *
        123491640037283275676800000000 := by
  calc
    _ ≤ ∑ k ∈ Finset.range 2855,
        (fineRho^2854 / fineScale^2 * (fineEnvelope k * fineEnvelope (2854-k))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ 2854 := by have := Finset.mem_range.mp hk; omega
      calc
        _ ≤ (fineRho^k * fineEnvelope k / fineScale) *
            (fineRho^(2854-k) * fineEnvelope (2854-k) / fineScale) :=
          mul_le_mul (exp31_fine_mass k) (exp31_fine_mass _)
            (exp31_mass_geometric _).1
            (div_nonneg (mul_nonneg (pow_nonneg (by norm_num [fineRho]) _) (fineEnvelope_nonneg _))
              (by norm_num [fineScale]))
        _ = _ := by rw [div_mul_div_comm,mul_mul_mul_comm,← pow_add,Nat.add_sub_of_le hk']; ring
    _ = fineRho^2854 / fineScale^2 *
        (∑ k ∈ Finset.range 2855, fineEnvelope k * fineEnvelope (2854-k)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left fine_envelope_convolution (by
      apply div_nonneg (pow_nonneg (by norm_num [fineRho]) _)
      positivity)

theorem fineRho_pow : fineRho^2854 ≤ (750351/10^23 : ℚ) := by norm_num [fineRho]

/-- The original printed rational bound, now discharged for the explicit matrix. -/
theorem exp31_transfer_bound : TransferMatrix5710Bound exp31Matrix5710 := by
  have hc := exp31_fine_convolution
  have hp := fineRho_pow
  have hs : (∑ k ∈ Finset.range 2855, transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k)) ≤
      (750351/10^23 : ℚ) / fineScale^2 * 123491640037283275676800000000 := by
    dsimp only [fineScale] at *
    linarith
  unfold TransferMatrix5710Bound lllRhs5710 transferContribution5710
  norm_num [t5710,beta5710,Finset.sum_Icc_succ_top]
  norm_num [fineScale] at hs
  linarith

end Se20Part
