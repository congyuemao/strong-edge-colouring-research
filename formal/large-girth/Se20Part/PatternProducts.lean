import Se20Part.RootedPatterns

noncomputable section
open scoped Classical BigOperators
open Finset
namespace Se20Part
set_option maxHeartbeats 2000000

abbrev RootPositions {n : ℕ} (f : SpanningPattern n) (k : ℕ) :=
  {i : Fin (n+1) // i.val ≠ k ∧ (f i).val ≠ 0}

def rootFactor {n : ℕ} (f : SpanningPattern n) (k : ℕ) (i : Fin (n+1)) : ℚ :=
  if i.val = k ∨ (f i).val = 0 then 1 else 2*3^(f i).val*t5710

theorem rootFactor_nonneg {n : ℕ} (f : SpanningPattern n) (k : ℕ) (i : Fin (n+1)) :
    0 ≤ rootFactor f k i := by
  unfold rootFactor
  split_ifs <;> norm_num [t5710,beta5710] <;> positivity

theorem rootedPatternWeight_eq {n k : ℕ} (hk : k ≤ n) (f : SpanningPattern n) :
    rootedPatternWeight k f = 3^n * ∏ i, rootFactor f k i := by
  let g : ℕ → ℚ := fun j => if j = k then 1 else transferLetterWeight (wordExtend f j)
  have hleft : (∏ j ∈ range k, transferLetterWeight (wordExtend f (n-(n-k+j+1)))) =
      ∏ j ∈ range k, g j := by
    calc
      _ = ∏ j ∈ range k, transferLetterWeight (wordExtend f (k-1-j)) := by
        apply prod_congr rfl
        intro j hj
        congr 2
        omega
      _ = ∏ j ∈ range k, transferLetterWeight (wordExtend f j) :=
        prod_range_reflect (fun j => transferLetterWeight (wordExtend f j)) k
      _ = _ := by
        apply prod_congr rfl
        intro j hj
        simp only [g,if_neg (show j ≠ k by have := mem_range.mp hj; omega)]
  have hright : (∏ j ∈ range (n-k), transferLetterWeight (wordExtend f (k+j+1))) =
      ∏ j ∈ range (n-k), g (k+1+j) := by
    apply prod_congr rfl
    intro j hj
    simp only [g,if_neg (show k+1+j ≠ k by omega)]
    congr 2
    omega
  have hprod : rootedPatternWeight k f = ∏ j ∈ range (n+1), g j := by
    rw [rootedPatternWeight,hleft,hright]
    have he : n+1 = (k+1)+(n-k) := by omega
    rw [he,prod_range_add,prod_range_succ]
    simp [g]
  have hall : (∏ j ∈ range (n+1), g j) =
      ∏ i : Fin (n+1), (if i.val = k then (1:ℚ) else 3) * rootFactor f k i := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro i _
    simp only [g,wordExtend_at,rootFactor,transferLetterWeight]
    split_ifs <;> simp_all <;> ring
  have hthree : (∏ i : Fin (n+1), if i.val = k then (1:ℚ) else 3) = 3^n := by
    let a : Fin (n+1) := ⟨k,by omega⟩
    have he (i : Fin (n+1)) : (i.val = k) ↔ i = a := by
      exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp_rw [he]
    rw [Fin.prod_univ_succAbove _ a]
    simp
  rw [hprod,hall,prod_mul_distrib,hthree]

theorem rootFactor_prod {n : ℕ} (f : SpanningPattern n) (k : ℕ) :
    (∏ i, rootFactor f k i) =
      (∏ i : RootPositions f k, (2*3^(f i.val).val : ℚ)) * t5710^(Fintype.card (RootPositions f k)) := by
  have he : (∏ i, rootFactor f k i) =
      ∏ i : RootPositions f k, (2*3^(f i.val).val*t5710 : ℚ) := by
    calc
      _ = ∏ i ∈ univ.filter (fun i : Fin (n+1) => i.val ≠ k ∧ (f i).val ≠ 0),
          (2*3^(f i).val*t5710 : ℚ) := by
        rw [prod_filter]
        apply prod_congr rfl
        intro i _
        simp only [rootFactor]
        split_ifs <;> simp_all
      _ = _ := prod_subtype (p := fun i : Fin (n+1) => i.val ≠ k ∧ (f i).val ≠ 0)
        _ (by simp) _
  rw [he,prod_mul_distrib,prod_const,card_univ]

theorem weighted_sum_injection {A B : Type*} [Fintype A] [Fintype B]
    (φ : A → B) (hi : Function.Injective φ) (w : B → ℚ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (φ a)) ≤ ∑ b, w b := by
  calc
    _ = ∑ b ∈ univ.image φ, w b := (sum_image (fun a _ b _ h => hi h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => hw b)

end Se20Part
