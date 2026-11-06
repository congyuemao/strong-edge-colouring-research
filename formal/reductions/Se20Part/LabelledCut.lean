import Se20Part.MatchingCutGeometry

noncomputable section
open scoped Classical
namespace Se20Part
variable {V I : Type*} [Fintype V] (G : SimpleGraph V)
local instance labelledCutDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- All crossing edges, labelled without repetition. Endpoints may repeat. -/
structure LabelledCut (I : Type*) where
  side : Finset V
  left : I → V
  right : I → V
  left_mem : ∀ i, left i ∈ side
  right_notMem : ∀ i, right i ∉ side
  adjacent : ∀ i, G.Adj (left i) (right i)
  pair_injective : Function.Injective (fun i => (left i,right i))
  complete : ∀ u ∈ side, ∀ v, v ∉ side → G.Adj u v →
    ∃ i, left i = u ∧ right i = v

namespace LabelledCut
variable {G} (C : LabelledCut G I)

def edge (i : I) : G.edgeSet := ⟨s(C.left i,C.right i),G.mem_edgeSet.mpr (C.adjacent i)⟩

def swap : LabelledCut G I where
  side := Finset.univ \ C.side
  left := C.right
  right := C.left
  left_mem i := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,C.right_notMem i⟩
  right_notMem i h := (Finset.mem_sdiff.mp h).2 (C.left_mem i)
  adjacent i := (C.adjacent i).symm
  pair_injective := by
    intro i j h
    exact C.pair_injective (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  complete u hu v hv huv := by
    have hvA : v ∈ C.side := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hv
    obtain ⟨i,hi,hj⟩ := C.complete v hvA u (Finset.mem_sdiff.mp hu).2 huv.symm
    exact ⟨i,hj,hi⟩

@[simp] theorem swap_edge (i : I) : C.swap.edge i = C.edge i := by
  apply Subtype.ext
  exact Sym2.eq_swap

theorem edge_injective : Function.Injective C.edge := by
  intro i j he
  have hp : s(C.left i,C.right i) = s(C.left j,C.right j) := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp hp with ⟨hl,hr⟩ | ⟨hl,_⟩
  · exact C.pair_injective (Prod.ext hl hr)
  · exact False.elim (C.right_notMem j (hl ▸ C.left_mem i))

theorem edge_not_side (i : I) : C.edge i ∉ sideEdges G C.side := by
  intro h
  exact C.right_notMem i ((mem_sideEdges G _ _).mp h _ (Sym2.mem_mk_right _ _))

theorem edge_not_other_side (i : I) : C.edge i ∉ sideEdges G (Finset.univ \ C.side) := by
  intro h
  exact (Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp h _
    (Sym2.mem_mk_left _ _))).2 (C.left_mem i)

theorem edge_cases (e : G.edgeSet) : e ∈ sideEdges G C.side ∨
    e ∈ sideEdges G (Finset.univ \ C.side) ∨ ∃ i, C.edge i = e := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  by_cases hu : u ∈ C.side <;> by_cases hv : v ∈ C.side
  · exact Or.inl ((mem_sideEdges G _ _).mpr (by intro w hw; rw [he] at hw; rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption))
  · obtain ⟨i,hi,hj⟩ := C.complete u hu v hv huv
    exact Or.inr (Or.inr ⟨i,Subtype.ext (by simpa only [edge,hi,hj] using he.symm)⟩)
  · obtain ⟨i,hi,hj⟩ := C.complete v hv u hu huv.symm
    exact Or.inr (Or.inr ⟨i,Subtype.ext (by simpa only [edge,hi,hj] using Sym2.eq_swap.trans he.symm)⟩)
  · apply Or.inr; apply Or.inl; apply (mem_sideEdges G _ _).mpr
    intro w hw
    rw [he] at hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩

theorem side_disjoint : Disjoint (sideEdges G C.side) (sideEdges G (Finset.univ \ C.side)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨u,v,heq⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hu : u ∈ e.val := heq ▸ Sym2.mem_mk_left u v
  exact (Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp hf u hu)).2
    ((mem_sideEdges G _ _).mp he u hu)

variable [Fintype I]

def multiplicity (v : V) : ℕ := (Finset.univ.filter (fun i => C.left i = v)).card

/-- Simplicity makes opposite endpoints distinct within each boundary fibre. -/
theorem fibre_neighbor_card (v : V) :
    (((Finset.univ.filter (fun i => C.left i = v)).image C.right)).card = C.multiplicity v := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj he
  exact C.pair_injective (Prod.ext
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) he)

theorem multiplicity_pos (i : I) : 1 ≤ C.multiplicity (C.left i) :=
  Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩

theorem multiplicity_zero {v : V} (hv : v ∉ C.side) : C.multiplicity v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hv ((Finset.mem_filter.mp hi).2 ▸ C.left_mem i)

theorem multiplicity_eq_cross {v : V} (hv : v ∈ C.side) :
    C.multiplicity v = (G.neighborFinset v \ C.side).card := by
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

theorem endpoint_budgets (hΔ : MaxDegreeFour G) (i : I) :
    (sideStar G C.side (C.left i)).card + C.multiplicity (C.left i) ≤ 4 ∧
    (sideNear G C.side (C.left i)).card ≤ (4 - C.multiplicity (C.left i)) * 4 := by
  let B := (Finset.univ.filter (fun j => C.left j = C.left i)).image C.right
  have hB : B ⊆ G.neighborFinset (C.left i) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact (G.mem_neighborFinset _ _).mpr ((Finset.mem_filter.mp hj).2 ▸ C.adjacent j)
  have hBA : Disjoint B C.side := by
    apply Finset.disjoint_left.mpr
    intro v hv hvA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact C.right_notMem j hvA
  simpa only [B,C.fibre_neighbor_card] using
    cut_endpoint_budgets G hΔ C.side (C.left_mem i) B hB hBA

/-- Repeated opposite endpoints add only the other stars in that fibre. -/
theorem conflict_cover (i : I) {e : G.edgeSet} (he : e ∈ sideEdges G C.side)
    (hie : (L2 G).Adj (C.edge i) e) :
    e ∈ sideNear G C.side (C.left i) ∨
      ∃ j, j ≠ i ∧ C.right j = C.right i ∧ e ∈ sideStar G C.side (C.left j) := by
  obtain ⟨_,u,hu,v,hv,huv⟩ := hie
  rcases Sym2.mem_iff.mp hu with rfl | rfl
  · exact Or.inl (Finset.mem_filter.mpr ⟨he,v,hv,huv.imp Eq.symm id⟩)
  · rcases huv with heq | hadj
    · exact False.elim (C.right_notMem i (heq.symm ▸ (mem_sideEdges G _ _).mp he v hv))
    · obtain ⟨j,hjL,hjR⟩ := C.complete v ((mem_sideEdges G _ _).mp he v hv)
        (C.right i) (C.right_notMem i) hadj.symm
      by_cases hj : j = i
      · subst j
        exact Or.inl (Finset.mem_filter.mpr ⟨he,v,hv,Or.inl hjL.symm⟩)
      · exact Or.inr ⟨j,hj,hjR,Finset.mem_inter.mpr
          ⟨(mem_incident G _ _).mpr (hjL.symm ▸ hv),he⟩⟩

theorem boundary_colour_budget (hΔ : MaxDegreeFour G)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) :
    (Finset.univ.biUnion (fun i => (sideStar G C.side (C.left i)).image φ.colour)).card +
      Fintype.card I ≤ 4 * (Finset.univ.image C.left).card := by
  let P := Finset.univ.image C.left
  have hsum : ∑ v ∈ P, C.multiplicity v = Fintype.card I := by
    exact (Finset.card_eq_sum_card_fiberwise
      (fun i (_ : i ∈ (Finset.univ : Finset I)) => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).symm
  have hlocal : ∀ v ∈ P, (sideStar G C.side v).card + C.multiplicity v ≤ 4 := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact (C.endpoint_budgets hΔ i).1
  have hu : Finset.univ.biUnion (fun i => (sideStar G C.side (C.left i)).image φ.colour) =
      P.biUnion (fun v => (sideStar G C.side v).image φ.colour) := by
    ext c
    simp [P]
  rw [hu,← hsum]
  calc
    _ ≤ (∑ v ∈ P, (sideStar G C.side v).card) + ∑ v ∈ P, C.multiplicity v := by
      apply Nat.add_le_add_right
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun v _ => Finset.card_image_le))
    _ = ∑ v ∈ P, ((sideStar G C.side v).card + C.multiplicity v) :=
      Finset.sum_add_distrib.symm
    _ ≤ ∑ _v ∈ P, 4 := Finset.sum_le_sum hlocal
    _ = _ := by simp [P,Nat.mul_comm]

end LabelledCut
end Se20Part
