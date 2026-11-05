import Se20Part.RouteQ

noncomputable section
open scoped Classical BigOperators
namespace Se20Part.Partition
variable {W : Type*} [Fintype W] (H : SimpleGraph W)

def degreeCount (π : W → Fin 10) (x : W) (n : ℤ) : ℕ :=
  (Finset.univ.filter (fun c => degreeIn H π x c = n)).card

theorem degreeCount_sum (π : W → Fin 10) (x : W) (n : ℤ) :
    (∑ c, if degreeIn H π x c = n then (1 : ℤ) else 0) = degreeCount H π x n := by
  simp only [degreeCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Full numerical classification in Lemma 4.2, when conflict degree is 24.
The five alternatives specify the multiplicities of degrees 3,4,5,6.
No degrees outside 2,…,6 occur. -/
theorem zeroClasses_profiles {π : W → Fin 10} (hπ : Minimum H π) (x : W)
    (hx : degreeIn H π x (π x) = 2) (h24 : H.degree x = 24) :
    (∀ c, 2 ≤ degreeIn H π x c ∧ degreeIn H π x c ≤ 6) ∧
    (let z := (zeroClasses H π x).card
     let a := degreeCount H π x 3
     let b := degreeCount H π x 4
     let c := degreeCount H π x 5
     let d := degreeCount H π x 6
     (z = 5 ∧ a = 4 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
     (z = 6 ∧ a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨
     (z = 7 ∧ a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨
     (z = 7 ∧ a = 0 ∧ b = 2 ∧ c = 0 ∧ d = 0) ∨
     (z = 8 ∧ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 1)) := by
  have hlo (c : Fin 10) : 2 ≤ degreeIn H π x c := by
    simpa [hx] using minimum_degreeIn_le H hπ x c
  have hsum : (∑ c : Fin 10, (degreeIn H π x c - 2)) = 4 := by
    simp [Finset.sum_sub_distrib, sum_degreeIn, h24]
  have hbounds (c : Fin 10) : 2 ≤ degreeIn H π x c ∧ degreeIn H π x c ≤ 6 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun c : Fin 10 => degreeIn H π x c - 2)
      (fun c _ => by have := hlo c; omega) (Finset.mem_univ c)
    rw [hsum] at h
    exact ⟨hlo c, by omega⟩
  refine ⟨hbounds, ?_⟩
  have hpoint (c : Fin 10) : degreeIn H π x c - 2 =
      (if degreeIn H π x c = 3 then 1 else 0) +
      2*(if degreeIn H π x c = 4 then 1 else 0) +
      3*(if degreeIn H π x c = 5 then 1 else 0) +
      4*(if degreeIn H π x c = 6 then 1 else 0) := by
    have := hbounds c
    split_ifs <;> omega
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, degreeCount_sum] at hsum
  have hparts : (degreeCount H π x 2 : ℤ) + degreeCount H π x 3 +
      degreeCount H π x 4 + degreeCount H π x 5 + degreeCount H π x 6 = 10 := by
    have hp (c : Fin 10) :
        (if degreeIn H π x c = 2 then (1 : ℤ) else 0) +
        (if degreeIn H π x c = 3 then 1 else 0) +
        (if degreeIn H π x c = 4 then 1 else 0) +
        (if degreeIn H π x c = 5 then 1 else 0) +
        (if degreeIn H π x c = 6 then 1 else 0) = 1 := by
      have := hbounds c
      split_ifs <;> omega
    have hs := congrArg (fun f : Fin 10 → ℤ => ∑ c, f c) (funext hp)
    simpa only [Finset.sum_add_distrib, degreeCount_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] using hs
  have hz : (zeroClasses H π x).card + 1 = degreeCount H π x 2 := by
    have he : zeroClasses H π x =
        (Finset.univ.filter (fun c => degreeIn H π x c = 2)).erase (π x) := by
      ext c
      simp [zeroClasses, and_comm]
    rw [he]
    exact Finset.card_erase_add_one (by simp [hx])
  dsimp only
  by_cases hd : degreeCount H π x 6 = 0
  · by_cases hc : degreeCount H π x 5 = 0
    · have hb : degreeCount H π x 4 ≤ 2 := by omega
      interval_cases h : degreeCount H π x 4
      · left; refine ⟨?_,?_,rfl,hc,hd⟩ <;> omega
      · right; left; refine ⟨?_,?_,rfl,hc,hd⟩ <;> omega
      · right; right; right; left; refine ⟨?_,?_,rfl,hc,hd⟩ <;> omega
    · right; right; left; refine ⟨?_,?_,?_,?_,hd⟩ <;> omega
  · right; right; right; right; refine ⟨?_,?_,?_,?_,?_⟩ <;> omega

end Se20Part.Partition
