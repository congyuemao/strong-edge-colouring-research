module

public import Se20Part.Legacy.Bounds.SubcubicDefect

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Equality in the complete-graph weighted bound forces the positive-weight
vertices to form a clique. This includes vertices of different positive weights. -/
theorem positive_weight_clique_of_complete_equality
    (S : Finset V) (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) (w : V → ℕ)
    (heq : (∑ x ∈ S, w x * ∑ y ∈ G.neighborFinset x, w y) + (∑ x ∈ S, w x ^ 2) =
      (∑ x ∈ S, w x) ^ 2) :
    G.IsClique (↑(S.filter (fun x => 0 < w x)) : Set V) := by
  let D := ∑ y ∈ S, w y
  have hb : ∀ x ∈ S, (∑ y ∈ G.neighborFinset x, w y) + w x ≤ D := by
    intro x hx
    have hc := sum_le_sum_of_subset_of_nonneg (f := w)
      (insert_subset hx (hclosed x hx)) (fun _ _ _ => Nat.zero_le _)
    rw [sum_insert (by simp)] at hc
    omega
  have hm : ∀ x ∈ S, w x * ((∑ y ∈ G.neighborFinset x, w y) + w x) ≤ w x * D :=
    fun x hx => Nat.mul_le_mul_left (w x) (hb x hx)
  have htotal : (∑ x ∈ S, w x * ((∑ y ∈ G.neighborFinset x, w y) + w x)) =
      ∑ x ∈ S, w x * D := by
    simpa only [mul_add, ← pow_two, sum_add_distrib, ← sum_mul, D] using heq
  have hlocal := (sum_eq_sum_iff_of_le hm).mp htotal
  intro x hx y hy hxy
  obtain ⟨hxS, hxw⟩ := mem_filter.mp hx
  obtain ⟨hyS, hyw⟩ := mem_filter.mp hy
  have hxbal : (∑ z ∈ G.neighborFinset x, w z) + w x = D := by
    have h := hlocal x hxS
    nlinarith
  by_contra hnot
  have hyn : y ∉ insert x (G.neighborFinset x) := by
    intro h
    exact (mem_insert.mp h).elim (Ne.symm hxy) (fun h => hnot ((G.mem_neighborFinset x y).mp h))
  have hsub : insert y (insert x (G.neighborFinset x)) ⊆ S :=
    insert_subset hyS (insert_subset hxS (hclosed x hxS))
  have hc := sum_le_sum_of_subset_of_nonneg (f := w) hsub (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert hyn, sum_insert (by simp)] at hc
  change _ ≤ D at hc
  omega

omit [Fintype V] in
/-- In a set of at most five vertices, the presence of a triangle-free edge
bounds the sum of internal degrees by fourteen. -/
theorem internal_degree_sum_le_fourteen_of_triangle_free_edge
    (S : Finset V) (hS : S.card ≤ 5) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (huv : G.Adj u v) (htri : ∀ w ∈ S, G.Adj u w → ¬ G.Adj v w) :
    (∑ x ∈ S, (S.filter (G.Adj x)).card) ≤ 14 := by
  let T := (S.erase u).erase v
  let d := fun x => (S.filter (G.Adj x)).card
  have huc : (S.erase u).card + 1 = S.card := card_erase_add_one hu
  have hvE : v ∈ S.erase u := mem_erase.mpr ⟨huv.ne.symm, hv⟩
  have hvc : T.card + 1 = (S.erase u).card := card_erase_add_one hvE
  have hT3 : T.card ≤ 3 := by omega
  have huT : u ∉ T := fun h => (mem_erase.mp (mem_erase.mp h).2).1 rfl
  have hvT : v ∉ T := notMem_erase _ _
  have hST : S = insert u (insert v T) := by
    rw [insert_erase hvE, insert_erase hu]
  have hdis : Disjoint (S.filter (G.Adj u)) (S.filter (G.Adj v)) := by
    apply disjoint_left.mpr
    intro w hwU hwV
    exact htri w (mem_filter.mp hwU).1 (mem_filter.mp hwU).2 (mem_filter.mp hwV).2
  have hduv : d u + d v ≤ 5 := by
    have hc := card_le_card (union_subset (filter_subset (G.Adj u) S) (filter_subset (G.Adj v) S))
    rw [card_union_of_disjoint hdis] at hc
    change d u + d v ≤ S.card at hc
    omega
  have hform (x : V) : d x = (T.filter (G.Adj x)).card +
      (if G.Adj x u then 1 else 0) + (if G.Adj x v then 1 else 0) := by
    have hun : u ∉ T.filter (G.Adj x) := fun h => huT (mem_filter.mp h).1
    have hvn : v ∉ T.filter (G.Adj x) := fun h => hvT (mem_filter.mp h).1
    have hun' : u ∉ insert v (T.filter (G.Adj x)) := fun h => (mem_insert.mp h).elim huv.ne hun
    dsimp [d]
    conv_lhs => rw [hST, filter_insert, filter_insert]
    by_cases hxu : G.Adj x u <;> by_cases hxv : G.Adj x v <;>
      simp only [hxu, hxv, ite_true, ite_false, card_insert_of_notMem hun',
        card_insert_of_notMem hun, card_insert_of_notMem hvn]
    all_goals omega
  have hTbound : (∑ x ∈ T, (T.filter (G.Adj x)).card) ≤ 6 := by
    have hb : ∀ x ∈ T, (T.filter (G.Adj x)).card ≤ 2 := by
      intro x hx
      have hs : T.filter (G.Adj x) ⊆ T.erase x := by
        intro y hy
        obtain ⟨hyT, hxy⟩ := mem_filter.mp hy
        exact mem_erase.mpr ⟨hxy.ne.symm, hyT⟩
      have hc := card_le_card hs
      have he := card_erase_add_one hx
      omega
    have hs := sum_le_sum hb
    simp only [sum_const, smul_eq_mul] at hs
    omega
  have hsumT : (∑ x ∈ T, d x) = (∑ x ∈ T, (T.filter (G.Adj x)).card) +
      (T.filter (G.Adj u)).card + (T.filter (G.Adj v)).card := by
    calc
      _ = ∑ x ∈ T, ((T.filter (G.Adj x)).card +
          (if G.Adj x u then 1 else 0) + (if G.Adj x v then 1 else 0)) := sum_congr rfl (fun x _ => hform x)
      _ = _ := by simp only [sum_add_distrib, G.adj_comm _ u, G.adj_comm _ v,
        ← sum_filter, sum_const, smul_eq_mul, mul_one]
  have huform := hform u
  have hvform := hform v
  simp only [G.loopless.irrefl, huv, huv.symm, ite_false, ite_true, add_zero] at huform hvform
  have hsumu := sum_erase_add S d hu
  have hsumv := sum_erase_add (S.erase u) d hvE
  change (∑ x ∈ S, d x) ≤ 14
  change (∑ x ∈ T, d x) + d v = _ at hsumv
  omega

theorem selected_labels_disjoint_internal_neighbors
    (Q : Finset G.edgeSet) (L : Finset V)
    (hno : ∀ e ∈ Q, ¬ ∀ x ∈ e.val, x ∈ L) {x : V} (hx : x ∈ L) :
    (L.filter (G.Adj x)).card + (edgeIncidences G Q x).card ≤ G.degree x := by
  have hs : L.filter (G.Adj x) ∪ rootLabels G Q x ⊆ G.neighborFinset x := by
    apply union_subset
    · intro y hy; exact (G.mem_neighborFinset x y).mpr (mem_filter.mp hy).2
    · exact rootLabels_subset_neighbors G Q x
  have hdis : Disjoint (L.filter (G.Adj x)) (rootLabels G Q x) := by
    apply disjoint_left.mpr
    intro y hy hl
    obtain ⟨_, e, heQ, he⟩ := mem_filter.mp hl
    apply hno e heQ
    rw [he, Sym2.forall_mem_pair]
    exact ⟨hx, (mem_filter.mp hy).1⟩
  have hc := card_le_card hs
  simpa only [card_union_of_disjoint hdis, rootLabels_card, SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem closed_unit_weight_adj_eq_internal_sum
    (S L : Finset V) (hLS : L ⊆ S)
    (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) (w : V → ℕ)
    (hw : ∀ x ∈ S, w x = if x ∈ L then 1 else 0) :
    (∑ x ∈ S, w x * ∑ y ∈ G.neighborFinset x, w y) =
      ∑ x ∈ L, (L.filter (G.Adj x)).card := by
  have hp : ∀ x ∈ S, w x * (∑ y ∈ G.neighborFinset x, w y) =
      if x ∈ L then (L.filter (G.Adj x)).card else 0 := by
    intro x hx
    rw [hw x hx]
    by_cases hxL : x ∈ L
    · simp only [hxL, ite_true, one_mul]
      have hfilter : (G.neighborFinset x).filter (fun y => y ∈ L) = L.filter (G.Adj x) := by
        ext y
        simp only [mem_filter, SimpleGraph.mem_neighborFinset, and_comm]
      calc
        _ = ∑ y ∈ G.neighborFinset x, if y ∈ L then 1 else 0 :=
          sum_congr rfl (fun y hy => hw y (hclosed x hx hy))
        _ = _ := by simp only [← sum_filter, sum_const, smul_eq_mul, mul_one, hfilter]
    · simp only [hxL, ite_false, zero_mul]
  have hfilter : S.filter (fun x => x ∈ L) = L := by
    ext x
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hLS h, h⟩⟩
  calc
    _ = ∑ x ∈ S, if x ∈ L then (L.filter (G.Adj x)).card else 0 := sum_congr rfl hp
    _ = _ := by rw [← sum_filter, hfilter]

theorem no_selected_inside_clique_of_card_ge_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    (L : Finset V) (hc : G.IsClique (L : Set V)) (hL : 3 ≤ L.card) :
    ∀ e ∈ Q, ¬ ∀ x ∈ e.val, x ∈ L := by
  intro e heQ hinside
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.property)
  have hu := hinside u (hev ▸ Sym2.mem_mk_left u v)
  have hv := hinside v (hev ▸ Sym2.mem_mk_right u v)
  have hvE := mem_erase.mpr ⟨huv.ne.symm, hv⟩
  have he1 := card_erase_add_one hu
  have he2 := card_erase_add_one hvE
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < ((L.erase u).erase v).card by omega)
  have hwL := (mem_erase.mp (mem_erase.mp hw).2).2
  exact subcubic_large_no_triangle_on_selected_edge G hΔ Q hQ hd hq e heQ hev.symm
    (hc hu hwL (mem_erase.mp (mem_erase.mp hw).2).1.symm)
    (hc hv hwL (mem_erase.mp hw).1.symm)

theorem no_selected_inside_internal_degree_bound
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3)
    (L : Finset V) (hno : ∀ e ∈ Q, ¬ ∀ x ∈ e.val, x ∈ L) :
    (∑ x ∈ L, (L.filter (G.Adj x)).card) ≤ L.card + ∑ x ∈ L, selectedDefect G Q x := by
  have hs := sum_le_sum (s := L) (fun x hx =>
    (selected_labels_disjoint_internal_neighbors G Q L hno hx).trans (hΔ x))
  have he : (∑ x ∈ L, ((edgeIncidences G Q x).card + selectedDefect G Q x)) = 3 * L.card := by
    calc
      _ = ∑ _x ∈ L, 3 := sum_congr rfl (fun x _ => Nat.add_sub_of_le (hd x))
      _ = _ := by simp [Nat.mul_comm]
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at hs he
  omega

end Se20Part.Legacy
