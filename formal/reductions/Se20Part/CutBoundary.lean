import Se20Part.LabelledCutGluing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance cutBoundaryDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Crossing edges oriented from the chosen side to its complement. Each
unordered crossing edge occurs once, even when endpoints repeat. -/
def cutBoundary (A : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2)

theorem cutBoundary_card (A : Finset V) :
    (cutBoundary G A).card = ∑ v ∈ A, (G.neighborFinset v \ A).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := A) (fun p hp => (Finset.mem_filter.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,_,hn,ha⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr (he ▸ ha),hn⟩
  · intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  · intro w hw
    obtain ⟨hwN,hwA⟩ := Finset.mem_sdiff.mp hw
    exact ⟨(v,w),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hv,hwA,(G.mem_neighborFinset _ _).mp hwN⟩,rfl⟩,rfl⟩

/-- Canonically label all crossing edges; no matching assumption is imposed. -/
def labelledBoundary (A : Finset V) : LabelledCut G (Fin (cutBoundary G A).card) := by
  let e := (cutBoundary G A).equivFin.symm
  refine ⟨A,(fun i => (e i).val.1),(fun i => (e i).val.2),?_,?_,?_,?_,?_⟩
  · intro i; exact (Finset.mem_filter.mp (e i).prop).2.1
  · intro i; exact (Finset.mem_filter.mp (e i).prop).2.2.1
  · intro i; exact (Finset.mem_filter.mp (e i).prop).2.2.2
  · intro i j h; exact e.injective (Subtype.ext h)
  · intro u hu v hv huv
    let p : cutBoundary G A := ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,hv,huv⟩⟩
    refine ⟨e.symm p,?_,?_⟩ <;> simp [p]

theorem labelledBoundary_multiplicity (A : Finset V) (v : V) (hv : v ∈ A) :
    (labelledBoundary G A).multiplicity v = (G.neighborFinset v \ A).card := by
  let C := labelledBoundary G A
  rw [← C.fibre_neighbor_card]
  congr 1
  ext w
  constructor
  · intro hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    have he := (Finset.mem_filter.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr (he ▸ C.adjacent i),C.right_notMem i⟩
  · intro hw
    obtain ⟨hwN,hwA⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨i,hi,hj⟩ := C.complete v hv w hwA ((G.mem_neighborFinset _ _).mp hwN)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,hj⟩

theorem cutBoundary_compl (A : Finset V) :
    (cutBoundary G (Finset.univ \ A)).card = (cutBoundary G A).card := by
  apply Finset.card_bij (fun p _ => (p.2,p.1))
  · intro p hp
    obtain ⟨_,hp,hq,hpq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using hq,
      (Finset.mem_sdiff.mp hp).2,hpq.symm⟩
  · intro p _ q _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro p hp
    obtain ⟨_,hp,hq,hpq⟩ := Finset.mem_filter.mp hp
    exact ⟨(p.2,p.1),Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using hq,
      by simpa using hp,hpq.symm⟩,rfl⟩

theorem induce_degree_side (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v = (G.neighborFinset v.val ∩ A).card := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce v)
  simp only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree,Finset.toFinset_coe] at h
  simp only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at h ⊢
  exact h

/-- The exact degree-sum identity proves parity for every cut in a regular
graph; it does not presuppose connectivity or minimality. -/
theorem cutBoundary_degree_sum (A : Finset V) :
    (cutBoundary G A).card + 2 * (G.induce (A : Set V)).edgeFinset.card =
      ∑ v ∈ A, G.degree v := by
  have hinternal : ∑ v ∈ A, (G.neighborFinset v ∩ A).card =
      2 * (G.induce (A : Set V)).edgeFinset.card := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp_rw [induce_degree_side]
    exact (Finset.sum_coe_sort A (fun v => (G.neighborFinset v ∩ A).card)).symm
  rw [cutBoundary_card,← hinternal,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_sdiff_add_card_inter (G.neighborFinset v) A

theorem fourRegular_cut_even (hreg : FourRegular G) (A : Finset V) :
    Even (cutBoundary G A).card := by
  have h := cutBoundary_degree_sum G A
  change ∀ v, G.degree v = 4 at hreg
  simp only [hreg,Finset.sum_const,smul_eq_mul] at h
  refine ⟨2 * A.card - (G.induce (A : Set V)).edgeFinset.card,?_⟩
  omega

theorem fourRegular_nontrivial_cut_six (hreg : FourRegular G) (A : Finset V)
    (hfive : 5 ≤ (cutBoundary G A).card) : 6 ≤ (cutBoundary G A).card := by
  obtain ⟨k,hk⟩ := fourRegular_cut_even G hreg A
  omega

end Se20Part
