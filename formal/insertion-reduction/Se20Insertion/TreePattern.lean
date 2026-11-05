import Se20Insertion.RecolourGain

noncomputable section
open scoped Classical
set_option maxHeartbeats 2000000
namespace Se20Insertion.TreePattern

/-- Six near positions and three far positions on each of the six branches. -/
abbrev Branch := Bool × Fin 3
abbrev Position := Sum Branch (Branch × Fin 3)

def graph : SimpleGraph Position where
  Adj x y := x ≠ y ∧ match x,y with
    | .inl _, .inl _ => True
    | .inl i, .inr (j,_) => i.1 = j.1
    | .inr (i,_), .inl j => i.1 = j.1
    | .inr (i,_), .inr (j,_) => i = j
  symm := ⟨by
    rintro x y ⟨hne,h⟩
    refine ⟨hne.symm,?_⟩
    cases x with
    | inl i => cases y with
      | inl j => trivial
      | inr j => exact h.symm
    | inr i => cases y with
      | inl j => exact h.symm
      | inr j => exact h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem positions_card : Fintype.card Position = 24 := by decide

theorem three_choose_le (q : Fin 4) : q.val.choose 2 ≤ q.val := by fin_cases q <;> decide

theorem three_choose_eq_dvd (q : Fin 4) (h : q.val.choose 2 = q.val) : 3 ∣ q.val := by
  fin_cases q <;> norm_num at *

theorem ten_far_edges (q : Branch → Fin 4) (h : (∑ i, (q i).val) = 10) :
    (∑ i, (q i).val.choose 2) ≤ 9 := by
  have hle := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Branch)) => three_choose_le (q i))
  by_contra hn
  have heq : (∑ i, (q i).val.choose 2) = ∑ i, (q i).val := by omega
  have each := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset Branch)) => three_choose_le (q i))).mp heq
  have hd : 3 ∣ ∑ i, (q i).val := Finset.dvd_sum (fun i hi => three_choose_eq_dvd (q i) (each i hi))
  rw [h] at hd
  norm_num at hd

/-- Exact edge count of a selection, recorded by the two near counts and
the six far-branch counts. These counts retain all information relevant to edges. -/
def edgeNumber (n : Bool → Fin 4) (q : Branch → Fin 4) : ℕ :=
  ((n false).val + (n true).val).choose 2 +
    (n false).val * (∑ i : Fin 3, (q (false,i)).val) +
    (n true).val * (∑ i : Fin 3, (q (true,i)).val) + ∑ i, (q i).val.choose 2

theorem sixteen_positions_bound (n : Bool → Fin 4) (q : Branch → Fin 4)
    (hsize : (n false).val + (n true).val + (∑ i, (q i).val) = 16) :
    edgeNumber n q ≤ 54 := by
  let k := (n false).val + (n true).val
  let m₀ := ∑ i : Fin 3, (q (false,i)).val
  let m₁ := ∑ i : Fin 3, (q (true,i)).val
  have hm : (∑ i, (q i).val) = m₀ + m₁ := by simp [m₀,m₁,Fintype.sum_prod_type,Nat.add_comm]
  have h0 : m₀ ≤ 9 := calc
    _ ≤ ∑ _i : Fin 3, 3 := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (q (false,i)).isLt)
    _ = 9 := by simp
  have h1 : m₁ ≤ 9 := calc
    _ ≤ ∑ _i : Fin 3, 3 := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (q (true,i)).isLt)
    _ = 9 := by simp
  have hn0 := (n false).isLt
  have hn1 := (n true).isLt
  have hfar : (∑ i, (q i).val.choose 2) ≤ m₀ + m₁ :=
    (Finset.sum_le_sum (fun i _ => three_choose_le (q i))).trans hm.le
  have hb3 : (n false).val * m₀ + (n true).val * m₁ ≤ 3 * (m₀ + m₁) := by nlinarith
  have hb9 : (n false).val * m₀ + (n true).val * m₁ ≤ 9 * k := by dsimp [k]; nlinarith
  have hk : k ≤ 6 := by dsimp [k]; omega
  have htot : k + m₀ + m₁ = 16 := by dsimp [k]; omega
  change k.choose 2 + _ + _ + _ ≤ 54
  dsimp only [m₀,m₁] at *
  clear_value k
  interval_cases k <;> norm_num [Nat.choose] <;> try omega
  have ht := ten_far_edges q (by omega)
  omega

theorem sixteen_positions_nonadjacent (n : Bool → Fin 4) (q : Branch → Fin 4)
    (hsize : (n false).val + (n true).val + (∑ i, (q i).val) = 16) :
    66 ≤ 120 - edgeNumber n q := by have := sixteen_positions_bound n q hsize; omega

abbrev Near (N : Bool → Finset (Fin 3)) := Σ s : Bool, N s
abbrev Far (B : Branch → Finset (Fin 3)) := Σ i : Branch, B i

/-- An unordered edge is either two selected near positions, a near and a
far position on the same side, or two far positions on the same branch.
The three tagged cases are disjoint and have no orientation duplication. -/
abbrev SelectedEdges (N : Bool → Finset (Fin 3)) (B : Branch → Finset (Fin 3)) :=
  ↥((Finset.univ : Finset (Near N)).powersetCard 2) ⊕
    ((Σ s : Bool, (N s) × (Σ i : Fin 3, B (s,i))) ⊕
      (Σ i : Branch, ↥((B i).powersetCard 2)))

theorem selected_edges_bound (N : Bool → Finset (Fin 3)) (B : Branch → Finset (Fin 3))
    (hsize : Fintype.card (Near N) + Fintype.card (Far B) = 16) :
    Fintype.card (SelectedEdges N B) ≤ 54 ∧
      66 ≤ (Fintype.card (Near N) + Fintype.card (Far B)).choose 2 - Fintype.card (SelectedEdges N B) := by
  let n (s : Bool) : Fin 4 := ⟨(N s).card, by have := Finset.card_le_univ (N s); simpa using Nat.lt_succ_of_le this⟩
  let q (i : Branch) : Fin 4 := ⟨(B i).card, by have := Finset.card_le_univ (B i); simpa using Nat.lt_succ_of_le this⟩
  have hN : Fintype.card (Near N) = (n false).val + (n true).val := by
    simp [Near,n,Nat.add_comm]
  have hB : Fintype.card (Far B) = ∑ i, (q i).val := by simp [Far,q]
  have he : Fintype.card (SelectedEdges N B) = edgeNumber n q := by
    simp only [SelectedEdges,Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ]
    simp [SelectedEdges,edgeNumber,Near,n,q,Finset.card_powersetCard,Fintype.sum_prod_type,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hb := sixteen_positions_bound n q (by omega)
  refine ⟨by omega,?_⟩
  rw [hsize,he]
  have hchoose : (16 : ℕ).choose 2 = 120 := by decide
  rw [hchoose]
  omega

end Se20Insertion.TreePattern
