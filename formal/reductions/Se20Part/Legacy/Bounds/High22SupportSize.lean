module

public import Se20Part.Legacy.Bounds.SubcubicDefect

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

theorem root_type_collision_inequality (r s e : ℕ) (he : e ≤ 1) (hr : r = s + e) :
    2 * r ≤ 2 + s * (r - 1) + e := by
  by_cases hr1 : r ≤ 1
  · omega
  have hrpos : r - 1 + 1 = r := by omega
  by_cases hs : 2 ≤ s
  · have hm := Nat.mul_le_mul_right (r - 1) hs
    omega
  · have hr2 : r = 2 := by omega
    have hs1 : s = 1 := by omega
    have he1 : e = 1 := by omega
    simp [hr2, hs1, he1]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The two-four-cycle budget at three selected root edges needs at least
eight distinct external endpoints, so the closed support has at least 13 points. -/
theorem high22_subcubic_seventeen_support_card_ge_thirteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    13 ≤ (selectedSupport G Q).card := by
  have hnot : ¬ ∀ x, (edgeIncidences G Q x).card ≤ 2 := by
    intro htwo
    have hc := clique_card_le_thirteen_of_support_degree_le_two G hΔ Q hQ htwo
    omega
  obtain ⟨r, hr⟩ := not_forall.mp hnot
  have hdr : (edgeIncidences G Q r).card = 3 := by have := hd r; omega
  have hrS : r ∈ selectedSupport G Q := mem_filter.mpr ⟨mem_univ _, by omega⟩
  have hreg : ∀ {x}, x ∈ selectedSupport G Q →
      G.degree x = 4 ∧ G.neighborFinset x ⊆ selectedSupport G Q :=
    fun {_} hx => subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx
  let A := G.neighborFinset r
  let R := rootLabels G Q r
  let B := selectedSupport G Q \ insert r A
  have hA : A.card = 4 := (hreg hrS).1
  have hR : R.card = 3 := by dsimp [R]; rw [rootLabels_card, hdr]
  have hRA : R ⊆ A := rootLabels_subset_neighbors G Q r
  have hAS : A ⊆ selectedSupport G Q := (hreg hrS).2
  have hN := high22_root_neighborhood_independent G hΔ Q h22 r
    (show 3 ≤ (rootLabels G Q r).card by change 3 ≤ R.card; omega)
  have hBcard : B.card + 5 = (selectedSupport G Q).card := by
    have hc := card_sdiff_add_card_eq_card (insert_subset hrS hAS)
    rw [card_insert_of_notMem (show r ∉ A by simp [A]), hA] at hc
    exact hc
  have hBx : ∀ x ∈ B, x ≠ r ∧ x ∉ A := by
    intro x hx
    have hn := (mem_sdiff.mp hx).2
    exact ⟨fun h => hn (h.symm ▸ mem_insert_self _ _), fun h => hn (mem_insert_of_mem h)⟩
  have hneighbors (a : V) (ha : a ∈ A) : B.filter (G.Adj a) = (G.neighborFinset a).erase r := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxB, hax⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨(hBx x hxB).1, (G.mem_neighborFinset a x).mpr hax⟩
    · intro hx
      obtain ⟨hxr, hxN⟩ := mem_erase.mp hx
      have hax := (G.mem_neighborFinset a x).mp hxN
      have hxS := (hreg (hAS ha)).2 hxN
      apply mem_filter.mpr
      refine ⟨mem_sdiff.mpr ⟨hxS, ?_⟩, hax⟩
      intro h
      rcases mem_insert.mp h with h | h
      · exact hxr h
      · exact hN ((G.mem_neighborFinset r a).mp ha) ((G.mem_neighborFinset r x).mp h) hax.ne hax
  have hNcard (a : V) (ha : a ∈ A) : (B.filter (G.Adj a)).card = 3 := by
    rw [hneighbors a ha]
    have hc := card_erase_add_one ((G.mem_neighborFinset a r).mpr ((G.mem_neighborFinset r a).mp ha).symm)
    have hda := (hreg (hAS ha)).1
    simp only [SimpleGraph.card_neighborFinset_eq_degree, hda] at hc
    omega
  have hdiff : (A \ R).card = 1 := by
    have hc := card_sdiff_add_card_eq_card hRA
    omega
  obtain ⟨b, hb⟩ := card_eq_one.mp hdiff
  have hbA : b ∈ A := (mem_sdiff.mp (hb.symm ▸ mem_singleton_self b)).1
  have hbR : b ∉ R := (mem_sdiff.mp (hb.symm ▸ mem_singleton_self b)).2
  have hAR : A = insert b R := by
    ext a
    constructor
    · intro ha
      by_cases haR : a ∈ R
      · exact mem_insert_of_mem haR
      · have hab := mem_singleton.mp (hb ▸ mem_sdiff.mpr ⟨ha, haR⟩)
        exact hab.symm ▸ mem_insert_self b R
    · intro ha
      exact (mem_insert.mp ha).elim (fun h => h.symm ▸ hbA) (fun h => hRA h)
  let k := fun x => (rootType G r x).card
  let s := fun x => (R.filter (G.Adj x)).card
  let eps := fun x => if G.Adj x b then 1 else 0
  have hk (x : V) : k x = s x + eps x := by
    have ht : rootType G r x = A.filter (G.Adj x) := rfl
    dsimp [k, s, eps]
    rw [ht, hAR, filter_insert]
    by_cases hxb : G.Adj x b
    · simp only [hxb, ite_true, card_insert_of_notMem (fun h => hbR (mem_filter.mp h).1)]
    · simp only [hxb, ite_false, add_zero]
  have hkSum : (∑ x ∈ B, k x) = 12 := by
    rw [show (∑ x ∈ B, k x) = ∑ a ∈ A, (B.filter (fun x => a ∈ rootType G r x)).card from
      root_type_card_sum_eq_label_sum G B r]
    calc
      _ = ∑ _a ∈ A, 3 := by
        apply sum_congr rfl
        intro a ha
        have heq : B.filter (fun x => a ∈ rootType G r x) = B.filter (G.Adj a) := by
          ext x
          simp only [mem_filter, mem_rootType, (G.mem_neighborFinset r a).mp ha, true_and, G.adj_comm x a]
        rw [heq, hNcard a ha]
      _ = _ := by simp [hA]
  have heSum : (∑ x ∈ B, eps x) = 3 := by
    have heq : (∑ x ∈ B, eps x) = (B.filter (G.Adj b)).card := by
      simp only [eps, card_eq_sum_ones, sum_filter, G.adj_comm b]
    rw [heq, hNcard b hbA]
  have hprod : (∑ x ∈ B, s x * (k x - 1)) ≤ 6 := by
    have heq : (∑ x ∈ B, s x * (k x - 1)) =
        ∑ a ∈ R, ∑ x ∈ B.filter (G.Adj a), (k x - 1) := by
      simp only [s, card_eq_sum_ones, sum_filter, sum_mul, ite_mul, one_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro x _
      simp only [G.adj_comm x a]
    have hbound : ∀ a ∈ R, (∑ x ∈ B.filter (G.Adj a), (k x - 1)) ≤ 2 := by
      intro a ha
      rw [hneighbors a (hRA ha)]
      have heq : (∑ x ∈ (G.neighborFinset a).erase r, (k x - 1)) =
          ∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card := by
        apply sum_congr rfl
        intro x hx
        have hax : a ∈ rootType G r x := (mem_rootType G r x a).mpr
          ⟨(G.mem_neighborFinset r a).mp (hRA ha),
            ((G.mem_neighborFinset a x).mp (mem_erase.mp hx).2).symm⟩
        have hc := card_erase_add_one hax
        change k x - 1 = _
        change _ + 1 = k x at hc
        omega
      rw [heq]
      exact high22_root_label_budget_two G hΔ Q h22 ha
    rw [heq]
    have hs := sum_le_sum hbound
    simpa only [sum_const, smul_eq_mul, hR] using hs
  have hpoint : ∀ x ∈ B, 2 * k x ≤ 2 + s x * (k x - 1) + eps x := by
    intro x _
    apply root_type_collision_inequality _ _ _ ?_ (hk x)
    dsimp [eps]
    split_ifs <;> omega
  have hs := sum_le_sum hpoint
  simp only [← mul_sum, sum_add_distrib, sum_const, smul_eq_mul, hkSum, heSum] at hs
  omega

theorem high22_subcubic_seventeen_support_card_thirteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    (selectedSupport G Q).card = 13 := by
  have hl := high22_subcubic_seventeen_support_card_ge_thirteen G hΔ Q hQ h22 hd hq
  have hu := subcubic_seventeen_support_card_le_thirteen G hΔ Q hQ hd hq
  omega

end Se20Part.Legacy
