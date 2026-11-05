import Se20Part.Partitions
import Se20Part.CycleLength

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
namespace Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)

def zeroClasses (π : W → C) (x : W) : Finset C :=
  Finset.univ.filter (fun c => c ≠ π x ∧ degreeIn H π x c = 2)

/-- Counting form of Lemmas 4.2 and 4.6':
z ≥ 3k − 1 − deg(x) whenever the own-class degree is two. -/
theorem zeroClasses_bound {π : W → C} (hπ : Minimum H π) (x : W)
    (hx : degreeIn H π x (π x) = 2) :
    3 * (Fintype.card C : ℤ) - 1 - H.degree x ≤ (zeroClasses H π x).card := by
  have hpoint (c : C) :
      (3 : ℤ) - (if c = π x then 1 else 0) -
        (if c ≠ π x ∧ degreeIn H π x c = 2 then 1 else 0) ≤ degreeIn H π x c := by
    have h := minimum_degreeIn_le H hπ x c
    by_cases hc : c = π x
    · subst c; simp [hx]
    · by_cases hd : degreeIn H π x c = 2
      · simp [hc, hd]
      · simp [hc, hd]; omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_degreeIn] at hs
  have hz : (∑ c : C, if c ≠ π x ∧ degreeIn H π x c = 2 then (1 : ℤ) else 0) =
      (zeroClasses H π x).card := by
    simp only [zeroClasses, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  rw [hz] at hs
  linarith

/-- Lemma 4.2's lower bound, including graphs of conflict degree below 24. -/
theorem zeroClasses_ten {π : W → Fin 10} (hπ : Minimum H π) (x : W)
    (hx : degreeIn H π x (π x) = 2) (hΔ : H.degree x ≤ 24) :
    5 ≤ (zeroClasses H π x).card := by
  have h := zeroClasses_bound H hπ x hx
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  omega

/-- The numerical ingredient of Lemma 4.6', not the triangle-exclusion claim. -/
theorem zeroClasses_nine_deficit {π : W → Fin 9} (hπ : Minimum H π) (x : W)
    (hx : degreeIn H π x (π x) = 2) (hΔ : H.degree x ≤ 24) :
    2 + (24 - H.degree x) ≤ (zeroClasses H π x).card := by
  have h := zeroClasses_bound H hπ x hx
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  omega

theorem degreeIn_update (π : W → C) (e : W) (j : C) (x : W) (c : C) :
    degreeIn H (Function.update π e j) x c = degreeIn H π x c +
      (if H.Adj x e ∧ j = c then 1 else 0) -
      (if H.Adj x e ∧ π e = c then 1 else 0) := by
  have hp (y : W) :
      (if H.Adj x y ∧ Function.update π e j y = c then (1 : ℤ) else 0) =
      (if H.Adj x y ∧ π y = c then (1 : ℤ) else 0) +
      (if y = e then (if H.Adj x e ∧ j = c then 1 else 0) -
        (if H.Adj x e ∧ π e = c then 1 else 0) else 0) := by
    by_cases hy : y = e
    · subst y; simp
    · simp [Function.update, hy]
  unfold degreeIn
  simp_rw [hp, Finset.sum_add_distrib]
  simp
  ring

/-- In a zero-cost target class, every neighbour has prior own degree ≤ 1.
Equality needs the odd-cycle minimality argument; Φ₁ alone gives only ≤ 1. -/
theorem zero_neighbour_degree_le_one {π : W → Fin 10} (hπ : Minimum H π)
    (hΔ : ∀ x, H.degree x ≤ 24) {e x : W} {j : Fin 10}
    (hj : j ≠ π e) (he : degreeIn H π e (π e) = 2)
    (hej : degreeIn H π e j = 2) (hx : π x = j) (hex : H.Adj e x) :
    degreeIn H π x j ≤ 1 := by
  have hm := minimum_update H hπ e j (hej.trans he.symm)
  have hb := minimum_ten_degree_le_two H hm hΔ x
  have hxe := hex.ne.symm
  simp only [Function.update_of_ne hxe, hx] at hb
  rw [degreeIn_update] at hb
  have hne : π e ≠ j := Ne.symm hj
  simp [hex.symm, hne] at hb
  omega

/-- Lemma 4.4. The path-end degree-one premise is explicit: it is the
conclusion of Lemma 4.3. The proof needs no girth or degree restriction. -/
theorem two_step_conditions {π : W → C} (hπ : Minimum H π)
    {e x : W} {j : C} (hj : j ≠ π e)
    (he : degreeIn H π e (π e) = 2) (hej : degreeIn H π e j = 2)
    (hx : π x = j) (hdx : degreeIn H π x j = 1) (hex : H.Adj e x) :
    (∀ k, k ≠ π e → k ≠ j → 2 ≤ degreeIn H π x k) ∧
      3 ≤ degreeIn H π x (π e) := by
  have hm := minimum_update H hπ e j (hej.trans he.symm)
  have hxe := hex.ne.symm
  have hb (k : C) := minimum_degreeIn_le H hm x k
  simp only [Function.update_of_ne hxe, hx, degreeIn_update] at hb
  have hne : π e ≠ j := Ne.symm hj
  constructor
  · intro k hk hjk
    have h := hb k
    simp [hex.symm, hne, hdx, Ne.symm hk, Ne.symm hjk] at h
    exact h
  · have h := hb (π e)
    simp [hex.symm, hne, hj, hdx] at h
    omega

end Partition

/-- Lemma 4.1's degree inequality for the manuscript's actual edge domain. -/
theorem routeQ_degree_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) {π : G.edgeSet → Fin 10}
    (hπ : Partition.Minimum (L2 G) π) (e : G.edgeSet) :
    Partition.degreeIn (L2 G) π e (π e) ≤ 2 := by
  apply Partition.minimum_ten_degree_le_two _ hπ _ e
  intro f
  have heq : (L2 G).neighborFinset f = conflicts G f := by ext x; simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, heq]
  exact card_conflicts_le_twentyFour G hΔ f

end Se20Part
