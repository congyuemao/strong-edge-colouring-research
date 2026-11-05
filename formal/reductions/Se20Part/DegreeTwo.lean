import Se20Part.CycleLength
import Se20Part.Partitions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

noncomputable section
open scoped Classical
namespace Se20Part

variable {W : Type*} [Fintype W] (H : SimpleGraph W)

/-- Two distinct neighbours exhaust a vertex of degree at most two. -/
theorem two_neighbours_exhaust (hΔ : ∀ v, H.degree v ≤ 2)
    {v a b z : W} (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b)
    (hz : H.Adj v z) : z = a ∨ z = b := by
  have hs : ({a,b} : Finset W) ⊆ H.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have he : ({a,b} : Finset W) = H.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le hs
    simpa [hab] using hΔ v
  have : z ∈ ({a,b} : Finset W) := he.symm ▸ (by simpa using hz)
  simpa using this

/-- A finite connected graph of maximum degree two is an ordered path, with
possibly the additional edge between its ends. The latter is allowed only for
at least three vertices, so isolated vertices and single edges are paths. -/
structure PathCycleOrder (H : SimpleGraph W) where
  size : ℕ
  pos : 0 < size
  vertex : Fin size ≃ W
  closed : Prop
  closed_size : closed → 3 ≤ size
  adj_iff : ∀ i j, H.Adj (vertex i) (vertex j) ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (closed ∧ ((i.val = 0 ∧ j.val + 1 = size) ∨
        (j.val = 0 ∧ i.val + 1 = size)))

theorem exists_pathCycleOrder (hconn : H.Connected) (hΔ : ∀ v, H.degree v ≤ 2) :
    Nonempty (PathCycleOrder H) := by
  letI : Nonempty W := hconn.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
  have hend (x : W) (hx : H.Adj u x) : x ∈ p.support := by
    by_contra hn
    have hh := hmax x v (p.cons hx.symm) (hp.cons hn)
    simp only [SimpleGraph.Walk.length_cons] at hh
    omega
  have hend' (x : W) (hx : H.Adj v x) : x ∈ p.support := by
    by_contra hn
    have hh := hmax x u (p.reverse.cons hx.symm)
      (hp.reverse.cons (by simpa using hn))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse] at hh
    omega
  have hinside (i : ℕ) (hi : 0 < i) (hil : i < p.length) {x : W}
      (hx : H.Adj (p.getVert i) x) :
      x = p.getVert (i-1) ∨ x = p.getVert (i+1) := by
    apply two_neighbours_exhaust H hΔ
      (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        (p.adj_getVert_succ (i := i-1) (by omega)).symm)
      (p.adj_getVert_succ hil) _ hx
    intro he
    have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
    omega
  have hclosed : ∀ x ∈ p.support, ∀ y, H.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    obtain ⟨i,hi,hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    subst x
    by_cases h0 : i = 0
    · subst i; exact hend y (by simpa using hxy)
    by_cases hl : i = p.length
    · subst i; exact hend' y (by simpa using hxy)
    rcases hinside i (by omega) (by omega) hxy with rfl | rfl <;>
      exact p.getVert_mem_support _
  have hsurj : ∀ x, x ∈ p.support := by
    intro x
    obtain ⟨q⟩ := hconn u x
    have go : ∀ {a b}, (q : H.Walk a b) → a ∈ p.support → b ∈ p.support := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hab q ih => exact fun ha => ih (hclosed _ ha _ hab)
    exact go q p.start_mem_support
  let f : Fin (p.length+1) → W := fun i => p.getVert i
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by simpa using Nat.le_of_lt_succ i.isLt)
        (by simpa using Nat.le_of_lt_succ j.isLt) hij
    · intro x
      obtain ⟨i,hi,hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hsurj x)
      exact ⟨⟨i,by omega⟩,hi⟩
  have hadj (i j : Fin (p.length+1)) (hij : H.Adj (f i) (f j)) :
      i.val+1 = j.val ∨ j.val+1 = i.val ∨
        (i.val = 0 ∧ j.val = p.length) ∨ (j.val = 0 ∧ i.val = p.length) := by
    have hn : i.val ≠ j.val := fun he => hij.ne (congrArg f (Fin.ext he))
    by_cases hi0 : i.val = 0 <;> by_cases hil : i.val = p.length
    · have hjl := j.isLt
      omega
    · by_cases hj0 : j.val = 0
      · omega
      by_cases hjl : j.val = p.length
      · exact Or.inr (Or.inr (Or.inl ⟨hi0,hjl⟩))
      rcases hinside j (by omega) (by omega) hij.symm with he | he
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
    · by_cases hj0 : j.val = 0
      · exact Or.inr (Or.inr (Or.inr ⟨hj0,hil⟩))
      by_cases hjl : j.val = p.length
      · omega
      rcases hinside j (by omega) (by omega) hij.symm with he | he
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
    · rcases hinside i (by omega) (by omega) hij with he | he
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
      · have := hp.getVert_injOn (by simp <;> omega) (by simp <;> omega) he
        omega
  refine ⟨⟨p.length+1, by omega, Equiv.ofBijective f hf,
    2 ≤ p.length ∧ H.Adj u v, fun h => by omega, ?_⟩⟩
  intro i j
  change H.Adj (f i) (f j) ↔ _
  constructor
  · intro hij
    rcases hadj i j hij with h | h | ⟨hi,hj⟩ | ⟨hj,hi⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases hl : p.length ≤ 1
      · have := hij.ne
        have := i.isLt
        have := j.isLt
        by_cases he : p.length = 0
        · have heq : i = j := Fin.ext (by omega)
          exact False.elim (hij.ne (congrArg f heq))
        · exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨by omega, by simpa [f,hi,hj] using hij⟩,
          Or.inl ⟨hi,by omega⟩⟩)
    · by_cases hl : p.length ≤ 1
      · by_cases he : p.length = 0
        · have heq : i = j := Fin.ext (by omega)
          exact False.elim (hij.ne (congrArg f heq))
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr ⟨⟨by omega, by simpa [f,hi,hj] using hij.symm⟩,
          Or.inr ⟨hj,by omega⟩⟩)
  · rintro (h | h | ⟨hc, (⟨hi,hj⟩ | ⟨hj,hi⟩)⟩)
    · change H.Adj (p.getVert i.val) (p.getVert j.val)
      rw [← h]
      exact p.adj_getVert_succ (by have := j.isLt; omega)
    · change H.Adj (p.getVert i.val) (p.getVert j.val)
      rw [← h]
      exact (p.adj_getVert_succ (by have := i.isLt; omega)).symm
    · have hj' : j.val = p.length := by omega
      simpa [f,hi,hj'] using hc.2
    · have hi' : i.val = p.length := by omega
      simpa [f,hi',hj] using hc.2.symm

theorem degree_induce_le (S : Set W) (x : S) :
    (H.induce S).degree x ≤ H.degree x.val := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map (f := Function.Embedding.subtype (· ∈ S)),
    SimpleGraph.map_neighborFinset_induce]
  exact Finset.card_le_card Finset.inter_subset_left

/-- The decomposition applies separately to every actual connected component. -/
theorem component_pathCycleOrder (hΔ : ∀ v, H.degree v ≤ 2)
    (C : H.ConnectedComponent) : Nonempty (PathCycleOrder C.toSimpleGraph) :=
  exists_pathCycleOrder _ C.connected_toSimpleGraph
    (fun x => (degree_induce_le H C.supp x).trans (hΔ x))

namespace PathCycleOrder
variable {H} (P : PathCycleOrder H)

theorem cycle_adj_indices {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔
      i.val+1 = j.val ∨ j.val+1 = i.val ∨
        (i.val = 0 ∧ j.val+1 = n) ∨ (j.val = 0 ∧ i.val+1 = n) := by
  rw [SimpleGraph.cycleGraph_adj']
  by_cases he : i = j
  · subst j
    rw [Fin.sub_val_of_le (le_refl i)]
    have := i.isLt
    omega
  by_cases hij : i ≤ j
  · rw [Fin.sub_val_of_le hij, Fin.val_sub,
      Nat.mod_eq_of_lt (show n - j.val + i.val < n by
        have := i.isLt; have := j.isLt; have : i.val ≠ j.val := fun h => he (Fin.ext h)
        change i.val ≤ j.val at hij; omega)]
    have := i.isLt; have := j.isLt
    change i.val ≤ j.val at hij
    omega
  · rw [Fin.sub_val_of_le (le_of_not_ge hij), Fin.val_sub,
      Nat.mod_eq_of_lt (show n - i.val + j.val < n by
        have := i.isLt; have := j.isLt
        change ¬ i.val ≤ j.val at hij; omega)]
    have := i.isLt; have := j.isLt
    change ¬ i.val ≤ j.val at hij
    omega

def cycleIso (hc : P.closed) : SimpleGraph.cycleGraph P.size ≃g H where
  toEquiv := P.vertex
  map_rel_iff' := by
    intro i j
    rw [P.adj_iff, cycle_adj_indices (P.closed_size hc)]
    simp [hc]

theorem card_size : Fintype.card W = P.size := by
  simpa using (Fintype.card_congr P.vertex).symm

theorem colourable (h : ¬ P.closed ∨ Even P.size) : H.Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun x => (⟨(P.vertex.symm x).val % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)) ?_⟩
  intro x y hxy he
  have hx := (P.vertex.symm x).isLt
  have hy := (P.vertex.symm y).isLt
  have he' := congrArg Fin.val he
  have hh := (P.adj_iff (P.vertex.symm x) (P.vertex.symm y)).mp (by simpa using hxy)
  rcases hh with hh | hh | ⟨hc,hh⟩
  · dsimp at he'; omega
  · dsimp at he'; omega
  · have heven : P.size % 2 = 0 := Nat.even_iff.mp (h.resolve_left (not_not.mpr hc))
    dsimp at he'
    rcases hh with ⟨hi,hj⟩ | ⟨hj,hi⟩ <;> omega

include P in
/-- Deleting any vertex of a path or cycle leaves a bipartite graph. The
explicit colouring also handles a deleted vertex at either end of a path. -/
theorem delete_vertex_colourable (z : W) : (H.induce {x | x ≠ z}).Colorable 2 := by
  let r := (P.vertex.symm z).val
  let col (x : {x : W // x ≠ z}) : Fin 2 :=
    ⟨(if (P.vertex.symm x.val).val < r then
      (P.vertex.symm x.val).val + P.size else (P.vertex.symm x.val).val) % 2,
      Nat.mod_lt _ (by omega)⟩
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro x y hxy he
  have hx := (P.vertex.symm x.val).isLt
  have hy := (P.vertex.symm y.val).isLt
  have hr : r < P.size := (P.vertex.symm z).isLt
  have hxr : (P.vertex.symm x.val).val ≠ r := by
    intro he
    exact x.prop (P.vertex.symm.injective (Fin.ext he))
  have hyr : (P.vertex.symm y.val).val ≠ r := by
    intro he
    exact y.prop (P.vertex.symm.injective (Fin.ext he))
  have he' := congrArg Fin.val he
  dsimp [col] at he'
  have hh := (P.adj_iff (P.vertex.symm x.val) (P.vertex.symm y.val)).mp
    (by simpa using hxy)
  split_ifs at he' <;>
    rcases hh with hh | hh | ⟨_, (⟨hi,hj⟩ | ⟨hj,hi⟩)⟩ <;> omega

def inducedCycle (hc : P.closed) : InducedCycle H P.size where
  vertex i := P.vertex ⟨i % P.size, Nat.mod_lt _ P.pos⟩
  three_le := P.closed_size hc
  injective i hi j hj he := by
    have := congrArg Fin.val (P.vertex.injective he)
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
  step i hi := by
    apply (P.adj_iff _ _).mpr
    left
    simp only [Nat.mod_eq_of_lt (show i < P.size by omega),
      Nat.mod_eq_of_lt (show i+1 < P.size by omega)]
  close := by
    apply (P.adj_iff _ _).mpr
    exact Or.inr (Or.inr ⟨hc, Or.inl ⟨by simp,
      by simp [Nat.mod_eq_of_lt (show P.size-1 < P.size by have := P.pos; omega)];
         have := P.pos; omega⟩⟩)
  no_chord i j hij hj hends hadj := by
    have hh := (P.adj_iff _ _).mp hadj
    simp only [Nat.mod_eq_of_lt (show i < P.size by omega), Nat.mod_eq_of_lt hj] at hh
    have := P.pos
    rcases hh with hh | hh | ⟨_, (⟨hi,hj⟩ | ⟨hj,hi⟩)⟩ <;> omega

theorem nonbipartite_closed_odd (h : ¬ H.Colorable 2) : P.closed ∧ Odd P.size := by
  constructor
  · by_contra hc
    exact h (P.colourable (Or.inl hc))
  · exact Nat.not_even_iff_odd.mp (fun he => h (P.colourable (Or.inr he)))

theorem colourable_iff : H.Colorable 2 ↔ ¬ P.closed ∨ Even P.size := by
  refine ⟨?_, P.colourable⟩
  intro hb
  by_cases hc : P.closed
  · right
    by_contra hn
    have hcol := (hb.some.comap (P.cycleIso hc).toHom).colorable.chromaticNumber_le
    rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd _ (by have := P.closed_size hc; omega)
      (Nat.not_even_iff_odd.mp hn)] at hcol
    norm_num at hcol
  · exact Or.inl hc

/-- Removing an arbitrary vertex of a cycle gives the path on n-1 vertices,
with its full induced adjacency, rather than merely a bipartite subgraph. -/
def deleteCycleIso (hc : P.closed) (z : W) :
    SimpleGraph.pathGraph (P.size-1) ≃g (H.induce {x | x ≠ z}) := by
  have hn := P.closed_size hc
  letI : NeZero P.size := ⟨by omega⟩
  let r := P.vertex.symm z
  let t (i : Fin (P.size-1)) : Fin P.size := ⟨i.val+1,by have := i.isLt; omega⟩
  have ht (i : Fin (P.size-1)) : t i ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp [t] at hh
  let f (i : Fin (P.size-1)) : {x : W // x ≠ z} :=
    ⟨P.vertex (t i + r), by
      intro he
      have he' : t i + r = r := P.vertex.injective (he.trans (P.vertex.apply_symm_apply z).symm)
      exact ht i (add_right_cancel (show t i + r = 0 + r by simpa using he'))⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      have hh : t i + r = t j + r := P.vertex.injective (congrArg Subtype.val hij)
      have hv := congrArg Fin.val (add_right_cancel hh)
      apply Fin.ext
      dsimp [t] at hv
      omega
    · intro x
      let q : Fin P.size := P.vertex.symm x.val - r
      have hq : q ≠ 0 := by
        intro h
        exact x.prop (P.vertex.symm.injective (sub_eq_zero.mp h))
      have hqp : 0 < q.val := by
        by_contra h
        apply hq
        apply Fin.ext
        rw [Fin.val_zero]
        omega
      let i : Fin (P.size-1) := ⟨q.val-1,by have := q.isLt; omega⟩
      refine ⟨i,Subtype.ext ?_⟩
      have hti : t i = q := Fin.ext (by dsimp [t,i]; omega)
      change P.vertex (t i + r) = x.val
      rw [hti]
      dsimp [q]
      rw [sub_add_cancel, P.vertex.apply_symm_apply]
  refine { toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := ?_ }
  intro i j
  change H.Adj (P.vertex (t i+r)) (P.vertex (t j+r)) ↔ _
  change H.Adj ((P.cycleIso hc) (t i+r)) ((P.cycleIso hc) (t j+r)) ↔ _
  rw [(P.cycleIso hc).map_adj_iff, SimpleGraph.cycleGraph_adj']
  simp only [add_sub_add_right_eq_sub]
  rw [← SimpleGraph.cycleGraph_adj', cycle_adj_indices hn, SimpleGraph.pathGraph_adj]
  dsimp [t]
  omega

theorem odd_cycle_deletion_even (hc : P.closed) (ho : Odd P.size) (z : W) :
    Even (Fintype.card {x : W // x ≠ z}) ∧
      Nonempty (SimpleGraph.pathGraph (P.size-1) ≃g (H.induce {x | x ≠ z})) := by
  refine ⟨?_,⟨P.deleteCycleIso hc z⟩⟩
  have he := Fintype.card_congr (P.deleteCycleIso hc z).toEquiv
  simp only [Fintype.card_fin] at he
  simp only [Fintype.card_eq_nat_card] at he ⊢
  apply he ▸ (show Even (P.size-1) from ?_)
  rw [Nat.even_iff]
  have hn := P.closed_size hc
  have hh := Nat.odd_iff.mp ho
  omega

theorem deleteCycleIso_endpoints (hc : P.closed) (z : W) (i : Fin (P.size-1)) :
    H.Adj z (P.deleteCycleIso hc z i).val ↔ i.val = 0 ∨ i.val+1 = P.size-1 := by
  have hn := P.closed_size hc
  letI : NeZero P.size := ⟨by omega⟩
  let r := P.vertex.symm z
  let t : Fin P.size := ⟨i.val+1,by have := i.isLt; omega⟩
  change H.Adj z (P.vertex (t+r)) ↔ _
  have hz : z = P.vertex (0+r) := by simp [r]
  rw [hz]
  change H.Adj ((P.cycleIso hc) (0+r)) ((P.cycleIso hc) (t+r)) ↔ _
  rw [(P.cycleIso hc).map_adj_iff, SimpleGraph.cycleGraph_adj']
  simp only [add_sub_add_right_eq_sub]
  rw [← SimpleGraph.cycleGraph_adj', cycle_adj_indices hn]
  simp only [Fin.val_zero]
  dsimp [t]
  have := i.isLt
  simp only [true_and]
  omega

end PathCycleOrder

namespace Partition
variable {C : Type*} [Fintype C]

/-- One graph on the original vertex type, retaining just monochromatic edges.
Its isolated vertices are retained, including those in singleton classes. -/
def monochrome (π : W → C) : SimpleGraph W where
  Adj x y := H.Adj x y ∧ π x = π y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun x h => H.irrefl h.1⟩

theorem monochrome_degree (π : W → C) (x : W) :
    ((monochrome H π).degree x : ℤ) = degreeIn H π x (π x) := by
  rw [degreeIn_eq_card, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 2
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  change (H.Adj x y ∧ π x = π y) ↔ (H.Adj x y ∧ π y = π x)
  simp [eq_comm]

/-- Φ₂ counts non-bipartite monochromatic components, once per component.
At a degree-two partition these are precisely the odd-cycle components. -/
def phi2 (π : W → C) : ℕ :=
  (Finset.univ.filter (fun K : (monochrome H π).ConnectedComponent =>
    ¬ K.toSimpleGraph.Colorable 2)).card

def MinimumTwo (π : W → C) : Prop :=
  Minimum H π ∧ ∀ σ : W → C, Minimum H σ → phi2 H π ≤ phi2 H σ

theorem exists_minimumTwo [Nonempty C] : ∃ π : W → C, MinimumTwo H π := by
  obtain ⟨π,hπ⟩ := exists_minimum H (C := C)
  let A : Finset (W → C) := Finset.univ.filter (Minimum H)
  obtain ⟨σ,hσ,hmin⟩ := A.exists_min_image (phi2 H) ⟨π,by simp [A,hπ]⟩
  exact ⟨σ, (Finset.mem_filter.mp hσ).2, fun τ hτ => hmin τ (by simp [A,hτ])⟩

/-- Lemma 4.1, including the path/cycle classification. -/
theorem minimum_ten_components {π : W → Fin 10} (hπ : Minimum H π)
    (hΔ : ∀ x, H.degree x ≤ 24) (K : (monochrome H π).ConnectedComponent) :
    Nonempty (PathCycleOrder K.toSimpleGraph) := by
  apply component_pathCycleOrder
  intro x
  have := minimum_ten_degree_le_two H hπ hΔ x
  rw [← monochrome_degree] at this
  exact_mod_cast this

theorem minimum_nine_components {π : W → Fin 9} (hπ : Minimum H π)
    (hΔ : ∀ x, H.degree x ≤ 24) (K : (monochrome H π).ConnectedComponent) :
    Nonempty (PathCycleOrder K.toSimpleGraph) := by
  apply component_pathCycleOrder
  intro x
  have := minimum_nine_degree_le_two H hπ hΔ x
  rw [← monochrome_degree] at this
  exact_mod_cast this

end Partition
end Se20Part

