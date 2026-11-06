import Se20Part.GallaiEndBlock
import Se20Part.EndBlockLists
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part

def highVertices {W : Type} [Fintype W] (H : SimpleGraph W) (k : ℕ) : Finset W :=
  Finset.univ.filter (fun v => H.degree v = k+1)

/-- A high vertex in an induced graph of maximum degree k+1 retains every
ambient neighbour, and in particular was already high in the ambient graph. -/
theorem induced_high_retains_neighbours {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hΔ : ∀ v, H.degree v ≤ k+1)
    (A : Finset W) (v : A) (hv : (H.induce (A : Set W)).degree v = k+1) :
    H.degree v.val = k+1 ∧ ∀ w, H.Adj v.val w → w ∈ A := by
  have hsub : A.filter (H.Adj v.val) ⊆ H.neighborFinset v.val := by
    intro w hw
    exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hw).2
  rw [degree_induce_finset] at hv
  have heq : A.filter (H.Adj v.val) = H.neighborFinset v.val :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [SimpleGraph.card_neighborFinset_eq_degree,hv]
      exact hΔ v.val)
  refine ⟨?_,?_⟩
  · rw [← SimpleGraph.card_neighborFinset_eq_degree,← heq,hv]
  · intro w hw
    exact (Finset.mem_filter.mp (heq.symm ▸ (H.mem_neighborFinset _ _).mpr hw)).1

theorem induced_high_clique {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hΔ : ∀ v, H.degree v ≤ k+1)
    (hQ : H.IsClique (highVertices H k : Set W)) (A : Finset W) :
    (H.induce (A : Set W)).IsClique (highVertices (H.induce (A : Set W)) k : Set A) := by
  intro u hu v hv huv
  have hu' := (induced_high_retains_neighbours H k hΔ A u (Finset.mem_filter.mp hu).2).1
  have hv' := (induced_high_retains_neighbours H k hΔ A v (Finset.mem_filter.mp hv).2).1
  exact hQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu'⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'⟩) (fun he => huv (Subtype.ext he))

/-- The exact parity reduction in A04: at most three high vertices in a
critical graph means exactly two, once the K5 case is excluded. -/
theorem four_critical_high_card_two {W : Type} [Fintype W]
    (H : SimpleGraph W) (hmin : VertexMinimalNoncolourable H 4)
    (hΔ : ∀ v, H.degree v ≤ 5)
    (hcl : ∀ B : Finset W, H.IsClique (B : Set W) → B.card ≤ 4)
    (hq : (highVertices H 4).card ≤ 3) : (highVertices H 4).card = 2 := by
  have hd : ∀ v, H.degree v = 4 ∨ H.degree v = 5 := by
    intro v
    have hl := vertex_minimal_noncolourable_degree H 4 hmin v
    have hu := hΔ v
    omega
  have heq : (Finset.univ.filter (fun v => Odd (H.degree v))) = highVertices H 4 := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,highVertices]
    rcases hd v with hh | hh <;> norm_num [hh]
  have heven := H.even_card_odd_degree_vertices
  rw [heq] at heven
  have hpos : (highVertices H 4).card ≠ 0 := by
    intro hz
    have hreg : ∀ v, H.degree v ≤ 4 := by
      intro v
      rcases hd v with hh | hh
      · omega
      · have hv : v ∈ highVertices H 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
        rw [Finset.card_eq_zero.mp hz] at hv
        exact (Finset.notMem_empty _ hv).elim
    exact hmin.1 (colourable_of_degree_le_no_clique H 4 (by decide) hreg hcl)
  obtain ⟨m,hm⟩ := heven
  omega

/-- The two adjacent high vertices each have exactly four low neighbours.
This is the eight-port interface, before classifying the low block chain. -/
theorem four_critical_eight_ports {W : Type} [Fintype W]
    (H : SimpleGraph W) (hmin : VertexMinimalNoncolourable H 4)
    (hΔ : ∀ v, H.degree v ≤ 5)
    (hcl : ∀ B : Finset W, H.IsClique (B : Set W) → B.card ≤ 4)
    (hq : (highVertices H 4).card ≤ 3)
    (hQ : H.IsClique (highVertices H 4 : Set W)) :
    ∃ u v, u ≠ v ∧ H.Adj u v ∧ highVertices H 4 = {u,v} ∧
      (H.neighborFinset u \ highVertices H 4).card = 4 ∧
      (H.neighborFinset v \ highVertices H 4).card = 4 := by
  obtain ⟨u,v,huv,hpair⟩ := Finset.card_eq_two.mp (four_critical_high_card_two H hmin hΔ hcl hq)
  have hu : u ∈ highVertices H 4 := hpair.symm ▸ Finset.mem_insert_self _ _
  have hv : v ∈ highVertices H 4 := hpair.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hadj := hQ hu hv huv
  have count (a b : W) (ha : a ∈ highVertices H 4) (hab : H.Adj a b)
      (he : highVertices H 4 = {a,b}) : (H.neighborFinset a \ highVertices H 4).card = 4 := by
    have hd := (Finset.mem_filter.mp ha).2
    have hN : H.neighborFinset a ∩ highVertices H 4 = {b} := by
      ext x
      rw [he]
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hx,hxa | hxb⟩
        · exact (hx.ne hxa.symm).elim
        · exact hxb
      · rintro rfl
        exact ⟨hab,Or.inr rfl⟩
    have hc := Finset.card_sdiff_add_card_inter (H.neighborFinset a) (highVertices H 4)
    rw [hN,Finset.card_singleton,SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  exact ⟨u,v,huv,hadj,hpair,count u v hu hadj hpair,
    count v u hv hadj.symm (by rw [hpair,Finset.pair_comm])⟩

end Se20Part
