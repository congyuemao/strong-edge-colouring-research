import Se20Part.ConflictBounds

/-! Finite partitions. `energy` is twice Φ₁; integer arithmetic avoids truncated
subtraction. All minima quantify over every partition, not just local moves. -/
noncomputable section
open scoped Classical BigOperators
namespace Se20Part
namespace Partition
variable {W C : Type*} [Fintype W] [Fintype C]
variable (H : SimpleGraph W)

def degreeIn (π : W → C) (x : W) (c : C) : ℤ :=
  ∑ y, if H.Adj x y ∧ π y = c then 1 else 0

def energy (π : W → C) : ℤ :=
  ∑ x, ∑ y, if H.Adj x y ∧ π x = π y then 1 else 0

def Minimum (π : W → C) : Prop := ∀ σ : W → C, energy H π ≤ energy H σ

theorem degreeIn_nonneg (π : W → C) (x : W) (c : C) : 0 ≤ degreeIn H π x c := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs <;> omega

theorem degreeIn_eq_card (π : W → C) (x : W) (c : C) :
    degreeIn H π x c = ((Finset.univ.filter (fun y => H.Adj x y ∧ π y = c)).card : ℤ) := by
  simp only [degreeIn, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem sum_degreeIn (π : W → C) (x : W) :
    ∑ c, degreeIn H π x c = (H.degree x : ℤ) := by
  simp only [degreeIn]
  rw [Finset.sum_comm]
  simp_rw [ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have he : Finset.univ.filter (H.Adj x) = H.neighborFinset x := by ext y; simp
  rw [← he]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem energy_update (π : W → C) (x : W) (c : C) :
    energy H (Function.update π x c) = energy H π +
      2 * (degreeIn H π x c - degreeIn H π x (π x)) := by
  have point (u v : W) :
      (if H.Adj u v ∧ Function.update π x c u = Function.update π x c v then (1 : ℤ) else 0) =
      (if H.Adj u v ∧ π u = π v then (1 : ℤ) else 0) +
      (if u = x then (if H.Adj x v ∧ π v = c then (1 : ℤ) else 0) -
        (if H.Adj x v ∧ π v = π x then 1 else 0) else 0) +
      (if v = x then (if H.Adj x u ∧ π u = c then (1 : ℤ) else 0) -
        (if H.Adj x u ∧ π u = π x then 1 else 0) else 0) := by
    by_cases hu : u = x <;> by_cases hv : v = x
    · subst u; subst v; simp
    · subst u; simp [Function.update, hv, eq_comm]
    · subst v; simp [Function.update, hu, H.adj_comm]
    · simp [Function.update, hu, hv]
  unfold energy
  simp_rw [point, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_sub_distrib]
  unfold degreeIn
  ring

/-- Lemma 4.1, the exchange inequality, for any finite graph. -/
theorem minimum_degreeIn_le {π : W → C} (hπ : Minimum H π) (x : W) (c : C) :
    degreeIn H π x (π x) ≤ degreeIn H π x c := by
  have h := hπ (Function.update π x c)
  rw [energy_update] at h
  omega

theorem minimum_mul_own_le {π : W → C} (hπ : Minimum H π) (x : W) :
    (Fintype.card C : ℤ) * degreeIn H π x (π x) ≤ H.degree x := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset C))
    (fun c _ => minimum_degreeIn_le H hπ x c)
  simpa [sum_degreeIn] using h

theorem minimum_ten_degree_le_two {π : W → Fin 10} (hπ : Minimum H π)
    (hΔ : ∀ x, H.degree x ≤ 24) (x : W) : degreeIn H π x (π x) ≤ 2 := by
  have := minimum_mul_own_le H hπ x
  have hb : (H.degree x : ℤ) ≤ 24 := by exact_mod_cast hΔ x
  simp only [Fintype.card_fin, Nat.cast_ofNat] at this
  omega

theorem minimum_nine_degree_le_two {π : W → Fin 9} (hπ : Minimum H π)
    (hΔ : ∀ x, H.degree x ≤ 24) (x : W) : degreeIn H π x (π x) ≤ 2 := by
  have := minimum_mul_own_le H hπ x
  have hb : (H.degree x : ℤ) ≤ 24 := by exact_mod_cast hΔ x
  simp only [Fintype.card_fin, Nat.cast_ofNat] at this
  omega

/-- Zero-cost moves preserve the global minimum, so exchanges may be iterated. -/
theorem minimum_update {π : W → C} (hπ : Minimum H π) (x : W) (c : C)
    (hc : degreeIn H π x c = degreeIn H π x (π x)) :
    Minimum H (Function.update π x c) := by
  intro σ
  simpa [energy_update, hc] using hπ σ

/-- Lovász's weighted potential (twice the manuscript's Ψ). -/
def weightedEnergy (d : C → ℕ) (π : W → C) : ℤ :=
  energy H π - 2 * ∑ x, (d (π x) : ℤ)

def WeightedMinimum (d : C → ℕ) (π : W → C) : Prop :=
  ∀ σ, weightedEnergy H d π ≤ weightedEnergy H d σ

theorem exists_minimum [Nonempty C] : ∃ π : W → C, Minimum H π := by
  obtain ⟨π,_,hπ⟩ := (Finset.univ : Finset (W → C)).exists_min_image
    (energy H) Finset.univ_nonempty
  exact ⟨π, fun σ => hπ σ (Finset.mem_univ _)⟩

theorem exists_weighted_minimum [Nonempty C] (d : C → ℕ) :
    ∃ π : W → C, WeightedMinimum H d π := by
  obtain ⟨π,_,hπ⟩ := (Finset.univ : Finset (W → C)).exists_min_image
    (weightedEnergy H d) Finset.univ_nonempty
  exact ⟨π, fun σ => hπ σ (Finset.mem_univ _)⟩

theorem weightedEnergy_update (d : C → ℕ) (π : W → C) (x : W) (c : C) :
    weightedEnergy H d (Function.update π x c) = weightedEnergy H d π +
      2 * ((degreeIn H π x c - d c) - (degreeIn H π x (π x) - d (π x))) := by
  have hs : (∑ y, (d (Function.update π x c y) : ℤ)) =
      (∑ y, (d (π y) : ℤ)) + d c - d (π x) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    have he : ∑ y ∈ Finset.univ.erase x, (d (Function.update π x c y) : ℤ) =
        ∑ y ∈ Finset.univ.erase x, (d (π y) : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp [Function.update, (Finset.mem_erase.mp hy).1]
    rw [he]
    simp
    ring
  unfold weightedEnergy
  rw [energy_update, hs]
  ring

theorem weighted_minimum_slack_le {d : C → ℕ} {π : W → C}
    (hπ : WeightedMinimum H d π) (x : W) (c : C) :
    degreeIn H π x (π x) - d (π x) ≤ degreeIn H π x c - d c := by
  have h := hπ (Function.update π x c)
  rw [weightedEnergy_update] at h
  omega

/-- The Lovász partition argument is proved, rather than assumed. -/
theorem lovasz_degree_bound {d : C → ℕ} {π : W → C}
    (hπ : WeightedMinimum H d π)
    (hbudget : ∀ x, (H.degree x : ℤ) < ∑ c, ((d c : ℤ) + 1)) (x : W) :
    degreeIn H π x (π x) ≤ d (π x) := by
  by_contra h
  have heach : ∀ c, (d c : ℤ) + 1 ≤ degreeIn H π x c := by
    intro c
    have := weighted_minimum_slack_le H hπ x c
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => heach c)
  rw [sum_degreeIn] at hs
  exact (not_le_of_gt (hbudget x)) hs

theorem lovasz_partition [Nonempty C] (d : C → ℕ)
    (hbudget : ∀ x, (H.degree x : ℤ) < ∑ c, ((d c : ℤ) + 1)) :
    ∃ π : W → C, WeightedMinimum H d π ∧ ∀ x, degreeIn H π x (π x) ≤ d (π x) := by
  obtain ⟨π,hπ⟩ := exists_weighted_minimum H d
  exact ⟨π,hπ,lovasz_degree_bound H hπ hbudget⟩

end Partition
end Se20Part
