import Se20Insertion.HoleCycleRank

noncomputable section
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Se20Insertion.TreePattern

def weight (S : Finset Position) (x : Position) : ℚ := if x ∈ S then 1 else 0

theorem weight_sq (S : Finset Position) (x : Position) : weight S x ^ 2 = weight S x := by
  by_cases hx : x ∈ S <;> simp [weight,hx]

theorem sum_members {X : Type*} [Fintype X] (S : Finset X) (f : X → ℚ) :
    (∑ x ∈ S, f x) = ∑ x : X, if x ∈ S then f x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x; simp

def nearCount (S : Finset Position) (s : Bool) : Fin 4 :=
  ⟨(Finset.univ.filter (fun i : Fin 3 => Sum.inl (s,i) ∈ S)).card,
    by have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin 3))) (p := fun i => Sum.inl (s,i) ∈ S)
       simpa using Nat.lt_succ_of_le this⟩

def farCount (S : Finset Position) (i : Branch) : Fin 4 :=
  ⟨(Finset.univ.filter (fun j : Fin 3 => Sum.inr (i,j) ∈ S)).card,
    by have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin 3))) (p := fun j => Sum.inr (i,j) ∈ S)
       simpa using Nat.lt_succ_of_le this⟩

theorem nearCount_cast (S : Finset Position) (s : Bool) :
    ((nearCount S s).val : ℚ) = ∑ i : Fin 3, weight S (.inl (s,i)) := by
  simp only [nearCount,weight,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem farCount_cast (S : Finset Position) (i : Branch) :
    ((farCount S i).val : ℚ) = ∑ j : Fin 3, weight S (.inr (i,j)) := by
  simp only [farCount,weight,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem selection_card (S : Finset Position) :
    (nearCount S false).val + (nearCount S true).val + (∑ i, (farCount S i).val) = S.card := by
  have hs : (S.card : ℚ) = ∑ x : Position, weight S x := by
    have hm := sum_members S (fun _ : Position => (1 : ℚ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hm
    refine hm.trans ?_
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [weight,hx]
  have heq : ((nearCount S false).val : ℚ) + (nearCount S true).val +
      ∑ i, ((farCount S i).val : ℚ) = S.card := by
    rw [hs]
    simp_rw [nearCount_cast,farCount_cast]
    simp [Fintype.sum_sum_type,Fintype.sum_prod_type,add_comm,add_assoc]
  exact_mod_cast heq

theorem weighted_edges (S : Finset Position) :
    (2 : ℚ) * ComponentInsertion.edges graph S =
      ∑ x : Position, ∑ y : Position, if graph.Adj x y then weight S x * weight S y else 0 := by
  have hs := ComponentInsertion.twice_edges graph S
  have hs' : (2 : ℚ) * ComponentInsertion.edges graph S =
      ∑ x ∈ S, ((S.filter (graph.Adj x)).card : ℚ) := by exact_mod_cast hs
  rw [hs']
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [sum_members]
  apply Finset.sum_congr rfl; intro x _
  rw [sum_members]
  by_cases hx : x ∈ S
  · simp only [hx,ite_true]
    apply Finset.sum_congr rfl; intro y _
    by_cases hy : y ∈ S <;> by_cases hxy : graph.Adj x y <;> simp [weight,hx,hy,hxy]
  · simp [hx,weight]

/-- A direct check of the adjacency matrix connects the structured count
to the actual induced edge set of the 24-vertex simple graph. -/
theorem actual_edge_count (S : Finset Position) :
    ComponentInsertion.edges graph S = edgeNumber (nearCount S) (farCount S) := by
  have hp : (2 : ℚ) * ComponentInsertion.edges graph S =
      2 * (edgeNumber (nearCount S) (farCount S) : ℚ) := by
    rw [weighted_edges]
    simp only [edgeNumber,Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_choose_two]
    simp_rw [nearCount_cast,farCount_cast]
    simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_succ,graph]
    ring_nf
    simp only [weight_sq]
    ring
  exact_mod_cast (show (ComponentInsertion.edges graph S : ℚ) = edgeNumber (nearCount S) (farCount S) from by linarith)

/-- The requested kernel-checked finite statement about the exact conflict pattern. -/
theorem sixteen_induced_edges (S : Finset Position) (hS : S.card = 16) :
    Nat.card (graph.induce (S : Set Position)).edgeSet ≤ 54 ∧
      66 ≤ S.card.choose 2 - Nat.card (graph.induce (S : Set Position)).edgeSet := by
  have hs := selection_card S
  have hb := sixteen_positions_bound (nearCount S) (farCount S) (by omega)
  have he := actual_edge_count S
  change ComponentInsertion.edges graph S ≤ 54 ∧ 66 ≤ S.card.choose 2 - ComponentInsertion.edges graph S
  rw [he,hS]
  have hc : (16 : ℕ).choose 2 = 120 := by decide
  rw [hc]
  omega

end Se20Insertion.TreePattern
