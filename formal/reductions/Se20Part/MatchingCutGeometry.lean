import Se20Part.CutGeometry
import Se20Part.FiveCutPalette

noncomputable section
open scoped Classical
namespace Se20Part
variable {V I : Type*} [Fintype V] (G : SimpleGraph V)
local instance matchingCutGeometryDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A labelled matching cut. Completeness lists all ambient crossing edges,
including witnesses of conflicts between two already coloured edges. -/
structure MatchingCut (I : Type*) where
  side : Finset V
  left : I → V
  right : I → V
  left_mem : ∀ i, left i ∈ side
  right_notMem : ∀ i, right i ∉ side
  adjacent : ∀ i, G.Adj (left i) (right i)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  complete : ∀ u ∈ side, ∀ v, v ∉ side → G.Adj u v →
    ∃ i, left i = u ∧ right i = v

namespace MatchingCut
variable {G} (C : MatchingCut G I)

def edge (i : I) : G.edgeSet := ⟨s(C.left i,C.right i),G.mem_edgeSet.mpr (C.adjacent i)⟩

def swap : MatchingCut G I where
  side := Finset.univ \ C.side
  left := C.right
  right := C.left
  left_mem i := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,C.right_notMem i⟩
  right_notMem i h := (Finset.mem_sdiff.mp h).2 (C.left_mem i)
  adjacent i := (C.adjacent i).symm
  left_injective := C.right_injective
  right_injective := C.left_injective
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
  rcases Sym2.eq_iff.mp hp with ⟨hl,_⟩ | ⟨hl,_⟩
  · exact C.left_injective hl
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

/-- With a matching cut, a cut edge's conflicts on one side are exactly
the edges touching its endpoint or a side-neighbour of that endpoint. -/
theorem cut_conflict_near (i : I) {f : G.edgeSet} (hf : f ∈ sideEdges G C.side)
    (hif : (L2 G).Adj (C.edge i) f) : f ∈ sideNear G C.side (C.left i) := by
  obtain ⟨_,u,hu,v,hv,huv⟩ := hif
  refine Finset.mem_filter.mpr ⟨hf,?_⟩
  rcases Sym2.mem_iff.mp hu with rfl | rfl
  · exact ⟨v,hv,huv.imp Eq.symm id⟩
  · rcases huv with he | hadj
    · exact False.elim (C.right_notMem i (he.symm ▸ (mem_sideEdges G _ _).mp hf v hv))
    · have hvA := (mem_sideEdges G _ _).mp hf v hv
      obtain ⟨j,hjL,hjR⟩ := C.complete v hvA (C.right i) (C.right_notMem i) hadj.symm
      have hj : j = i := C.right_injective hjR
      subst j
      exact ⟨v,hv,Or.inl hjL.symm⟩

theorem endpoint_counts (hΔ : MaxDegreeFour G) (i : I) :
    (sideStar G C.side (C.left i)).card ≤ 3 ∧
    (sideNear G C.side (C.left i)).card ≤ 12 := by
  have h := cut_endpoint_budgets G hΔ C.side (C.left_mem i) {C.right i}
    (by intro v hv; simp only [Finset.mem_singleton] at hv; subst v; simpa using C.adjacent i)
    (by simpa only [Finset.disjoint_singleton_left] using C.right_notMem i)
  simp only [Finset.card_singleton] at h
  omega

end MatchingCut
end Se20Part
