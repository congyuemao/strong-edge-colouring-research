module

public import Se20Part.Legacy.Bounds.SubcubicSeventeen

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All defect sums below are restricted to selectedSupport. -/
def selectedDefect (Q : Finset G.edgeSet) (x : V) : ℕ :=
  3 - (edgeIncidences G Q x).card

omit [Fintype V] [DecidableEq V] in
theorem neighbor_weight_sum_swap (S : Finset V) (f g : V → ℕ) :
    (∑ x ∈ S, f x * ∑ y ∈ S.filter (G.Adj x), g y) =
      ∑ y ∈ S, g y * ∑ x ∈ S.filter (G.Adj y), f x := by
  simp only [sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  simp only [G.adj_comm x y, Nat.mul_comm]

omit [DecidableEq V] in
theorem neighbor_filter_eq_of_closed (S : Finset V)
    (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) {x : V} (hx : x ∈ S) :
    S.filter (G.Adj x) = G.neighborFinset x := by
  ext y
  exact ⟨fun h => (G.mem_neighborFinset x y).mpr (mem_filter.mp h).2,
    fun h => mem_filter.mpr ⟨hclosed x hx h, (G.mem_neighborFinset x y).mp h⟩⟩

omit [DecidableEq V] in
theorem closed_neighbor_weight_sum_swap (S : Finset V)
    (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) (f g : V → ℕ) :
    (∑ x ∈ S, f x * ∑ y ∈ G.neighborFinset x, g y) =
      ∑ y ∈ S, g y * ∑ x ∈ G.neighborFinset y, f x := by
  have hleft : (∑ x ∈ S, f x * ∑ y ∈ S.filter (G.Adj x), g y) =
      ∑ x ∈ S, f x * ∑ y ∈ G.neighborFinset x, g y := by
    apply sum_congr rfl
    intro x hx
    rw [neighbor_filter_eq_of_closed G S hclosed hx]
  have hright : (∑ y ∈ S, g y * ∑ x ∈ S.filter (G.Adj y), f x) =
      ∑ y ∈ S, g y * ∑ x ∈ G.neighborFinset y, f x := by
    apply sum_congr rfl
    intro y hy
    rw [neighbor_filter_eq_of_closed G S hclosed hy]
  rw [← hleft, ← hright]
  exact neighbor_weight_sum_swap G S f g

theorem selectedCoverEdges_weighted_double_count
    (Q : Finset G.edgeSet) (S : Finset V) (w : V → ℕ) :
    (∑ x ∈ S, w x * (selectedCoverEdges G Q x).card) =
      ∑ e ∈ Q, ∑ x ∈ S.filter (fun x => e ∈ selectedCoverEdges G Q x), w x := by
  have hf (x : V) : Q.filter (fun e => e ∈ selectedCoverEdges G Q x) = selectedCoverEdges G Q x := by
    ext e
    exact ⟨fun h => (mem_filter.mp h).2,
      fun h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1, h⟩⟩
  calc
    _ = ∑ x ∈ S, ∑ e ∈ Q, if e ∈ selectedCoverEdges G Q x then w x else 0 := by
      apply sum_congr rfl
      intro x _
      calc
        _ = w x * (Q.filter (fun e => e ∈ selectedCoverEdges G Q x)).card := by rw [hf x]
        _ = _ := by simp only [card_eq_sum_ones, sum_filter, mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ e ∈ Q, ∑ x ∈ S, if e ∈ selectedCoverEdges G Q x then w x else 0 := sum_comm
    _ = _ := by simp only [sum_filter]

theorem subcubic_seventeen_defect_cover_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    (∑ x ∈ endpointNeighbourCover G u v, selectedDefect G Q x) ≤ 2 := by
  have hc := clique_card_le_one_add_incidence_sum G Q hQ e heQ he
  have hcard := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd (by omega) e heQ he).1
  have heq : (∑ x ∈ endpointNeighbourCover G u v,
      ((edgeIncidences G Q x).card + selectedDefect G Q x)) = 18 := by
    calc
      _ = ∑ _x ∈ endpointNeighbourCover G u v, 3 := by
        apply sum_congr rfl
        intro x _
        exact Nat.add_sub_of_le (hd x)
      _ = _ := by simp [hcard]
  rw [sum_add_distrib] at heq
  omega

theorem subcubic_seventeen_defect_weighted_budget
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    (∑ x ∈ selectedSupport G Q, selectedDefect G Q x * (selectedCoverEdges G Q x).card) ≤ 34 := by
  rw [selectedCoverEdges_weighted_double_count]
  have hb : ∀ e ∈ Q, (∑ x ∈ (selectedSupport G Q).filter
      (fun x => e ∈ selectedCoverEdges G Q x), selectedDefect G Q x) ≤ 2 := by
    intro e heQ
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hs : (selectedSupport G Q).filter (fun x => e ∈ selectedCoverEdges G Q x) ⊆
        endpointNeighbourCover G u v := by
      intro x hx
      exact ((mem_selectedCoverEdges_iff G Q e hev.symm).mp (mem_filter.mp hx).2).2
    exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)).trans
      (subcubic_seventeen_defect_cover_le_two G hΔ Q hQ hd hq e heQ hev.symm)
  have hs := sum_le_sum hb
  simpa only [sum_const, smul_eq_mul, hq] using hs

theorem subcubic_seventeen_defect_balance
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17)
    {x : V} (hx : x ∈ selectedSupport G Q) :
    (selectedCoverEdges G Q x).card + (∑ y ∈ G.neighborFinset x, selectedDefect G Q y) =
      9 + selectedDefect G Q x := by
  have hreg := subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx
  have hcount := subcubic_large_selectedCoverEdges_count G hΔ Q hQ hd (by omega) x
  have heq : (∑ y ∈ G.neighborFinset x,
      ((edgeIncidences G Q y).card + selectedDefect G Q y)) = 12 := by
    calc
      _ = ∑ _y ∈ G.neighborFinset x, 3 := by
        apply sum_congr rfl
        intro y _
        exact Nat.add_sub_of_le (hd y)
      _ = _ := by simp [hreg.1]
  have hxsum : (edgeIncidences G Q x).card + selectedDefect G Q x = 3 := Nat.add_sub_of_le (hd x)
  rw [sum_add_distrib] at heq
  omega

theorem subcubic_seventeen_weighted_identity
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    (∑ x ∈ selectedSupport G Q, selectedDefect G Q x * (selectedCoverEdges G Q x).card) +
      (∑ x ∈ selectedSupport G Q, selectedDefect G Q x *
        ∑ y ∈ G.neighborFinset x, selectedDefect G Q y) =
      9 * (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) +
        ∑ x ∈ selectedSupport G Q, selectedDefect G Q x ^ 2 := by
  rw [← sum_add_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  have hb := subcubic_seventeen_defect_balance G hΔ Q hQ hd hq hx
  nlinarith

omit [DecidableEq V] in
theorem closed_four_regular_weight_square_bound (S : Finset V)
    (hreg : ∀ x ∈ S, G.degree x = 4 ∧ G.neighborFinset x ⊆ S) (w : V → ℕ) :
    (∑ x ∈ S, w x * ∑ y ∈ G.neighborFinset x, w y) ≤ 4 * ∑ x ∈ S, w x ^ 2 := by
  have hswap := closed_neighbor_weight_sum_swap G S (fun x hx => (hreg x hx).2)
    (fun _ => 1) (fun x => w x ^ 2)
  have hleft : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, w x ^ 2) = 4 * ∑ x ∈ S, w x ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, (hreg x hx).1]
  have hright : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, w y ^ 2) = 4 * ∑ x ∈ S, w x ^ 2 := by
    simp only [one_mul, sum_const, smul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree] at hswap
    rw [hswap, mul_sum]
    apply sum_congr rfl
    intro x hx
    rw [(hreg x hx).1, Nat.mul_comm]
  have hs := sum_le_sum (s := S) (fun x _ => sum_le_sum (s := G.neighborFinset x)
    (fun y _ => two_mul_le_add_sq (w x) (w y)))
  simp only [sum_add_distrib, ← mul_sum, mul_assoc] at hs
  rw [hleft, hright] at hs
  nlinarith

theorem closed_weight_square_complete_bound (S : Finset V)
    (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) (w : V → ℕ) :
    (∑ x ∈ S, w x * ∑ y ∈ G.neighborFinset x, w y) + (∑ x ∈ S, w x ^ 2) ≤
      (∑ x ∈ S, w x) ^ 2 := by
  have hs : ∀ x ∈ S, (∑ y ∈ G.neighborFinset x, w y) + w x ≤ ∑ y ∈ S, w y := by
    intro x hx
    have hsub : insert x (G.neighborFinset x) ⊆ S := insert_subset hx (hclosed x hx)
    have hc := sum_le_sum_of_subset_of_nonneg (f := w) hsub (fun _ _ _ => Nat.zero_le _)
    rw [sum_insert (by simp)] at hc
    omega
  have hm := sum_le_sum (s := S) (fun x hx => Nat.mul_le_mul_left (w x) (hs x hx))
  simpa only [mul_add, ← pow_two, sum_add_distrib, ← sum_mul] using hm

def selectedLowVertices (Q : Finset G.edgeSet) : Finset V :=
  (selectedSupport G Q).filter (fun x => 0 < selectedDefect G Q x)

def selectedLeafVertices (Q : Finset G.edgeSet) : Finset V :=
  (selectedSupport G Q).filter (fun x => selectedDefect G Q x = 2)

omit [DecidableRel G.Adj] in
theorem selectedDefect_le_two (Q : Finset G.edgeSet) {x : V}
    (hx : x ∈ selectedSupport G Q) : selectedDefect G Q x ≤ 2 := by
  have hpos := (mem_filter.mp hx).2
  dsimp [selectedDefect]
  omega

omit [DecidableRel G.Adj] in
theorem selected_defect_counts (Q : Finset G.edgeSet) :
    (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) =
      (selectedLowVertices G Q).card + (selectedLeafVertices G Q).card ∧
    (∑ x ∈ selectedSupport G Q, selectedDefect G Q x ^ 2) =
      (selectedLowVertices G Q).card + 3 * (selectedLeafVertices G Q).card := by
  have hlin (x : V) (hx : x ∈ selectedSupport G Q) : selectedDefect G Q x =
      (if 0 < selectedDefect G Q x then 1 else 0) +
        (if selectedDefect G Q x = 2 then 1 else 0) := by
    have hb := selectedDefect_le_two G Q hx
    split_ifs <;> omega
  have hsq (x : V) (hx : x ∈ selectedSupport G Q) : selectedDefect G Q x ^ 2 =
      (if 0 < selectedDefect G Q x then 1 else 0) +
        3 * (if selectedDefect G Q x = 2 then 1 else 0) := by
    have hb := selectedDefect_le_two G Q hx
    have he : selectedDefect G Q x = 0 ∨ selectedDefect G Q x = 1 ∨ selectedDefect G Q x = 2 := by omega
    rcases he with he | he | he <;> rw [he] <;> decide
  constructor
  · have hs := sum_congr rfl hlin
    simpa only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one,
      selectedLowVertices, selectedLeafVertices] using hs
  · have hs := sum_congr rfl hsq
    simpa only [sum_add_distrib, ← mul_sum, ← sum_filter, sum_const, smul_eq_mul, mul_one,
      selectedLowVertices, selectedLeafVertices] using hs

omit [DecidableRel G.Adj] in
theorem selected_defect_sum_handshake (Q : Finset G.edgeSet)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) :
    (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) + 2 * Q.card =
      3 * (selectedSupport G Q).card := by
  have hs : (∑ x ∈ selectedSupport G Q,
      ((edgeIncidences G Q x).card + selectedDefect G Q x)) =
      3 * (selectedSupport G Q).card := by
    calc
      _ = ∑ _x ∈ selectedSupport G Q, 3 := sum_congr rfl (fun x _ => Nat.add_sub_of_le (hd x))
      _ = _ := by simp [Nat.mul_comm]
  rw [sum_add_distrib, selectedSupport_incidence_sum] at hs
  omega

theorem subcubic_seventeen_low_card_le_five
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    (selectedLowVertices G Q).card ≤ 5 := by
  have hi := subcubic_seventeen_weighted_identity G hΔ Q hQ hd hq
  have hb := subcubic_seventeen_defect_weighted_budget G hΔ Q hQ hd hq
  have hr := closed_four_regular_weight_square_bound G (selectedSupport G Q)
    (fun x hx => subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx)
    (selectedDefect G Q)
  obtain ⟨hlin, hsq⟩ := selected_defect_counts G Q
  omega

theorem subcubic_seventeen_defect_square_inequality
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    9 * (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) +
        2 * (∑ x ∈ selectedSupport G Q, selectedDefect G Q x ^ 2) ≤
      34 + (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) ^ 2 := by
  have hi := subcubic_seventeen_weighted_identity G hΔ Q hQ hd hq
  have hb := subcubic_seventeen_defect_weighted_budget G hΔ Q hQ hd hq
  have hc := closed_weight_square_complete_bound G (selectedSupport G Q)
    (fun x hx => (subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx).2)
    (selectedDefect G Q)
  omega

/-- No conflict-degree threshold is needed to bound the support of the
remaining seventeen-edge subcubic clique by thirteen vertices. -/
theorem subcubic_seventeen_support_card_le_thirteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) :
    (selectedSupport G Q).card ≤ 13 := by
  have hl := subcubic_seventeen_low_card_le_five G hΔ Q hQ hd hq
  obtain ⟨hlin, hsq⟩ := selected_defect_counts G Q
  have hh := selected_defect_sum_handshake G Q hd
  have hsub : selectedLeafVertices G Q ⊆ selectedLowVertices G Q := by
    intro x hx
    obtain ⟨hxS, hx2⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxS, by omega⟩
  have hleaf := card_le_card hsub
  have hn : (selectedSupport G Q).card ≤ 14 := by omega
  by_contra hnot
  have hn14 : (selectedSupport G Q).card = 14 := by omega
  have hD8 : (∑ x ∈ selectedSupport G Q, selectedDefect G Q x) = 8 := by omega
  have hc := subcubic_seventeen_defect_square_inequality G hΔ Q hQ hd hq
  rw [hD8] at hc
  norm_num at hc
  omega

end Se20Part.Legacy
