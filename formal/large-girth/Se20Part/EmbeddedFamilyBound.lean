import Se20Part.FamilyEncoding

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem familyCode_mass {V : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (e : G.edgeSet) {n : ℕ} (hn : 0 < n) :
    (∑ c : FamilyCode G e n, codeWeight c) ≤
      8712 * ∑ k : Fin (n+1), transferMass exp31Matrix5710 k.val * transferMass exp31Matrix5710 (n-k.val) := by
  have hdSum : (∑ d : PositiveDepth, (3:ℚ)^d.val.val) = 363 := by decide +kernel
  have hinner (k : Fin (n+1)) (d : PositiveDepth) :
      (∑ f : RootedPattern n k.val (Nat.le_of_lt_succ k.isLt) d.val,
        ∑ c : EmbeddedPattern G e n k.val d.val.val f.val,
          t5710^(Fintype.card (RootPositions f.val k.val))) ≤
        24*3^d.val.val * (transferMass exp31Matrix5710 k.val * transferMass exp31Matrix5710 (n-k.val)) := by
    calc
      _ ≤ ∑ f : RootedPattern n k.val (Nat.le_of_lt_succ k.isLt) d.val,
          24*3^d.val.val*rootedPatternWeight k.val f.val := by
        apply sum_le_sum
        intro f _
        simpa only [sum_const,card_univ,nsmul_eq_mul] using
          embeddedPattern_weight hd hn e k.val d.val.val (Nat.le_of_lt_succ k.isLt) f.val
      _ = 24*3^d.val.val * ∑ f : RootedPattern n k.val (Nat.le_of_lt_succ k.isLt) d.val,
          rootedPatternWeight k.val f.val := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (rootedPattern_convolution hn (Nat.le_of_lt_succ k.isLt) d.val) (by positivity)
  calc
    _ = ∑ k : Fin (n+1), ∑ d : PositiveDepth,
        ∑ f : RootedPattern n k.val (Nat.le_of_lt_succ k.isLt) d.val,
        ∑ _c : EmbeddedPattern G e n k.val d.val.val f.val,
          t5710^(Fintype.card (RootPositions f.val k.val)) := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro k _
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro d _
      rw [Fintype.sum_sigma]
      rfl
    _ ≤ ∑ k : Fin (n+1), ∑ d : PositiveDepth,
        24*3^d.val.val*(transferMass exp31Matrix5710 k.val*transferMass exp31Matrix5710 (n-k.val)) :=
      sum_le_sum (fun k _ => sum_le_sum (fun d _ => hinner k d))
    _ = _ := by simp only [← sum_mul,← mul_sum,hdSum]; ring

theorem familyCode_mass_range {V : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (e : G.edgeSet) {n : ℕ} (hn : 0 < n) :
    (∑ c : FamilyCode G e n, codeWeight c) ≤
      8712 * ∑ k ∈ range (n+1), transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (n-k) := by
  have hh := familyCode_mass hd e hn
  rw [Fin.sum_univ_eq_sum_range (fun k => transferMass exp31Matrix5710 k *
    transferMass exp31Matrix5710 (n-k)) (n+1)] at hh
  exact hh

theorem rootedChain_bound {V I : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (E : Set G.edgeSet) (part : E → I) (e : E) :
    rootedChainCount G E part e ≤
      ((8712 * ∑ k ∈ range 2855, transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k) : ℚ) : ℝ) := by
  let B := {b : ChainBad G E part // e ∈ b.val}
  have hex (b : B) : ∃ c : FamilyCode G e.val 2854,
      codeEdges c = b.val.val.image Subtype.val ∧ codeWeight c = t5710^(b.val.val.card-1) := by
    obtain ⟨hs,u,v,Y,hy,hlen,F,hF,hinj⟩ := b.val.property.2.2
    exact familyCode_exists_length E b.val.val e b.property Y hy hlen (by norm_num) F hF hinj hs
  choose code hrec hw using hex
  have hi : Function.Injective code := by
    intro b c heq
    have hh := (hrec b).symm.trans ((congrArg codeEdges heq).trans (hrec c))
    apply Subtype.ext
    apply Subtype.ext
    exact (Finset.image_injective Subtype.val_injective) hh
  have hsum := weighted_sum_injection code hi codeWeight (fun c => pow_nonneg (by norm_num [t5710,beta5710]) _)
  have hs : (∑ b : B, t5710^(b.val.val.card-1)) ≤
      8712 * ∑ k ∈ range 2855, transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k) := by
    simp_rw [hw] at hsum
    exact hsum.trans (familyCode_mass_range hd e.val (by norm_num : 0 < 2854))
  have hc := Rat.cast_le (K := ℝ).mpr hs
  push_cast at hc
  unfold rootedChainCount
  rw [← sum_filter,sum_filter_subtype]
  simpa only [Rat.cast_mul,Rat.cast_sum,Rat.cast_pow,Rat.cast_ofNat] using hc

/-- Full embedded-family inequality from the second-pass specification. The
proof in fact does not need girth once the actual spanning families are given. -/
theorem transfer_spanning_family_bound : TransferMatrixSpanningFamilyBound := by
  intro V I _ _ G hd _hg E part _hsurj hsize i
  have hh := chain_per_part_of_rooted G E part hsize _ (rootedChain_bound hd E part) i
  apply hh.trans
  have hc : (0:ℚ) ≤ ∑ k ∈ range 2855,
      transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k) := by
    apply sum_nonneg
    intro k _
    exact mul_nonneg (exp31_mass_geometric _).1 (exp31_mass_geometric _).1
  have he : (∑ δ ∈ Icc 1 5, 12*(3:ℚ)^δ) = 4356 := by norm_num [sum_Icc_succ_top]
  have hnum : (1203/1000:ℚ)*(8712*∑ k ∈ range 2855,
      transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (2854-k)) ≤
      transferContribution5710 exp31Matrix5710 := by
    rw [transferContribution5710,he,beta5710]
    nlinarith
  have hreal := Rat.cast_le (K := ℝ).mpr hnum
  simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hreal

end Se20Part
