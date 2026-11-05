module

public import Se20Part.Legacy.PrivateExchange
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

noncomputable def privateFinset (M : Finset W) (v : W) : Finset W := by
  classical
  exact univ.filter (IsPrivate H M v)

omit [DecidableEq W] [DecidableRel H.Adj] in
@[simp] theorem mem_privateFinset (M : Finset W) (v x : W) :
    x ∈ privateFinset H M v ↔ IsPrivate H M v x := by
  classical
  simp [privateFinset]

def covering (M : Finset W) (x : W) : Finset W :=
  M.filter (fun v => x = v ∨ H.Adj x v)

noncomputable def privateOwners (M : Finset W) (x : W) : Finset W := by
  classical
  exact M.filter (fun v => IsPrivate H M v x)

theorem maximum_covers (M : Finset W) (hM : H.IsMaximumIndepSet M) (x : W) :
    ∃ v ∈ M, x = v ∨ H.Adj x v := by
  classical
  by_contra! hnone
  have hxout : x ∉ M := fun hx => (hnone x hx).1 rfl
  have hI : H.IsIndepSet (↑(insert x M) : Set W) := by
    intro a ha b hb hab
    change a ∈ insert x M at ha
    change b ∈ insert x M at hb
    simp only [mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact (hnone b hb).2
    · rcases hb with rfl | hb
      · intro hax
        exact (hnone a ha).2 (H.adj_symm hax)
      · exact hM.isIndepSet ha hb hab
  have hmax := hM.maximum (insert x M) hI
  rw [card_insert_of_notMem hxout] at hmax
  omega

omit [Fintype W] in
theorem private_iff_covering_singleton (M : Finset W) {v x : W} (hv : v ∈ M) :
    IsPrivate H M v x ↔ covering H M x = {v} := by
  classical
  constructor
  · intro hp
    ext w
    simp only [covering, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hw, hcov⟩
      by_contra hwv
      rcases hp.2 w hw hwv with ⟨hne, hno⟩
      exact hcov.elim hne hno
    · rintro rfl
      exact ⟨hv, hp.1⟩
  · intro heq
    have hvcover : v ∈ covering H M x := by simp [heq]
    refine ⟨(mem_filter.mp hvcover).2, ?_⟩
    intro w hw hwv
    have hnot : ¬ (x = w ∨ H.Adj x w) := by
      intro hcov
      have hwcover : w ∈ covering H M x := mem_filter.mpr ⟨hw, hcov⟩
      have : w = v := by simpa [heq] using hwcover
      exact hwv this
    exact not_or.mp hnot

theorem coverage_pointwise (M : Finset W) (hM : H.IsMaximumIndepSet M) (x : W) :
    2 ≤ (covering H M x).card + (privateOwners H M x).card := by
  classical
  obtain ⟨v, hv, hcov⟩ := maximum_covers H M hM x
  have hpos : 0 < (covering H M x).card :=
    card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, hcov⟩⟩
  by_cases hone : (covering H M x).card = 1
  · obtain ⟨m, hm⟩ := card_eq_one.mp hone
    have hmcov : m ∈ covering H M x := by simp [hm]
    have hmM : m ∈ M := (mem_filter.mp hmcov).1
    have hp : IsPrivate H M m x := (private_iff_covering_singleton H M hmM).2 hm
    have hpPos : 0 < (privateOwners H M x).card :=
      card_pos.mpr ⟨m, mem_filter.mpr ⟨hmM, hp⟩⟩
    omega
  · omega

theorem sum_covering (M : Finset W) :
    (∑ x : W, (covering H M x).card) = ∑ v ∈ M, (H.degree v + 1) := by
  classical
  have hclosed (v : W) :
      (univ.filter (fun x => x = v ∨ H.Adj x v)).card = H.degree v + 1 := by
    have heq : univ.filter (fun x => x = v ∨ H.Adj x v) =
        insert v (H.neighborFinset v) := by
      ext x
      simp [H.adj_comm]
    rw [heq, card_insert_of_notMem (H.notMem_neighborFinset_self v)]
    rfl
  simp only [covering, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simpa only [card_eq_sum_ones, sum_filter] using hclosed v

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem sum_privateOwners (M : Finset W) :
    (∑ x : W, (privateOwners H M x).card) = ∑ v ∈ M, (privateFinset H M v).card := by
  classical
  simp only [privateOwners, privateFinset, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- Double-counting closed-neighbourhood incidences, including private vertices. -/
theorem private_double_count (M : Finset W) (hM : H.IsMaximumIndepSet M) :
    2 * Fintype.card W ≤ ∑ v ∈ M, (H.degree v + 1 + (privateFinset H M v).card) := by
  classical
  have hp := sum_le_sum (s := (univ : Finset W))
    (fun x _ => coverage_pointwise H M hM x)
  simp only [sum_add_distrib, sum_covering, sum_privateOwners, sum_const,
    card_univ, smul_eq_mul] at hp
  simpa only [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_comm] using hp

/-- The abstract packing bound has its local numerical hypothesis explicitly exposed. -/
theorem packing_of_local_bound (M : Finset W) (hM : H.IsMaximumIndepSet M)
    (k : ℕ)
    (hlocal : ∀ v ∈ M, H.degree v + 1 + (privateFinset H M v).card ≤ 2 * k) :
    Fintype.card W ≤ k * M.card := by
  have hcount := private_double_count H M hM
  have hsum := sum_le_sum hlocal
  simp only [sum_const, smul_eq_mul] at hsum
  nlinarith

theorem private_card_le_degree_add_one (M : Finset W) (v : W) :
    (privateFinset H M v).card ≤ H.degree v + 1 := by
  classical
  have hsub : privateFinset H M v ⊆ insert v (H.neighborFinset v) := by
    intro x hx
    rcases (mem_privateFinset H M v x).mp hx with ⟨hcov, _⟩
    simpa only [mem_insert, SimpleGraph.mem_neighborFinset, H.adj_comm] using hcov
  have hcard := card_le_card hsub
  simpa only [card_insert_of_notMem (H.notMem_neighborFinset_self v),
    SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-- Explicit structural assumptions still needed for the 20-packing application. -/
structure CliqueThresholds20 : Prop where
  max_degree : ∀ v : W, H.degree v ≤ 24
  high20 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 20 ≤ H.degree x) → Q.card ≤ 19
  high21 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 21 ≤ H.degree x) → Q.card ≤ 18
  high22 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 22 ≤ H.degree x) → Q.card ≤ 17
  high23 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 23 ≤ H.degree x) → Q.card ≤ 16
  high24 : ∀ Q : Finset W, H.IsClique (Q : Set W) →
    (∀ x ∈ Q, 24 ≤ H.degree x) → Q.card ≤ 7

theorem local20_of_thresholds (ht : CliqueThresholds20 H)
    (M : Finset W) (hM : IsOptimal H M) {v : W} (hv : v ∈ M) :
    H.degree v + 1 + (privateFinset H M v).card ≤ 40 := by
  classical
  have hc : H.IsClique (↑(privateFinset H M v) : Set W) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx)
      ((mem_privateFinset H M v y).mp hy) hxy
  have hm : ∀ x ∈ privateFinset H M v, H.degree v ≤ H.degree x := by
    intro x hx
    exact private_degree_mono H M hM hv ((mem_privateFinset H M v x).mp hx)
  by_cases hlow : H.degree v ≤ 19
  · have := private_card_le_degree_add_one H M v
    omega
  have hmax := ht.max_degree v
  by_cases h20 : H.degree v = 20
  · have := ht.high20 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h21 : H.degree v = 21
  · have := ht.high21 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h22 : H.degree v = 22
  · have := ht.high22 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  by_cases h23 : H.degree v = 23
  · have := ht.high23 _ hc (fun x hx => by have := hm x hx; omega)
    omega
  have := ht.high24 _ hc (fun x hx => by have := hm x hx; omega)
  omega

/-- Conditional theorem: the structural clique thresholds are explicit hypotheses. -/
theorem packing20_of_thresholds (ht : CliqueThresholds20 H) :
    ∃ M : Finset W, H.IsMaximumIndepSet M ∧ Fintype.card W ≤ 20 * M.card := by
  obtain ⟨M, hM⟩ := optimal_exists H
  exact ⟨M, hM.1, packing_of_local_bound H M hM.1 20
    (fun v hv => local20_of_thresholds H ht M hM hv)⟩

end Se20Part.Legacy
