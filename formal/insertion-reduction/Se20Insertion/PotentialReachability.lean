import Se20Insertion.ClassSquarePotential

noncomputable section
open scoped Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {W : Type*} [DecidableEq W] (H : SimpleGraph W)

/-- A partial colouring with a designated uncoloured vertex. -/
def HoleState := {s : (Σ F : Finset W, PartialColouring H F) × W // s.2 ∉ s.1.1}

namespace HoleState
variable {H}
def make {F : Finset W} (φ : PartialColouring H F) (e : W) (he : e ∉ F) : HoleState H :=
  ⟨(⟨F,φ⟩,e),he⟩

def potential (s : HoleState H) : ℤ := s.val.1.2.classSquare

/-- Only legal hole moves and actual nonempty component swaps are edges. -/
inductive Step : HoleState H → HoleState H → Prop
  | hole {F : Finset W} (φ : PartialColouring H F) {e f : W} {p : Colour}
      (he : e ∉ F) (hs : φ.Single e p f) :
      Step (make φ e he) (make (φ.holeMove hs) f (by simp [hs.1.2.1.ne.symm]))
  | kempe {F : Finset W} (φ : PartialColouring H F) (e : W) (he : e ∉ F)
      (a b : Colour) (hab : a ≠ b) (x : W) (hx : x ∈ φ.Bicoloured a b) :
      Step (make φ e he)
        (make (φ.swap a b {y | φ.SameComponent a b x y} (φ.component_closed a b x)) e he)

def Reachable (s t : HoleState H) : Prop := Relation.ReflTransGen Step s t

instance [Finite W] : Finite (HoleState H) := by
  unfold HoleState
  infer_instance

/-- The maximum is in the actual reachable class of the supplied initial state. -/
theorem exists_reachable_maximum [Finite W] (s : HoleState H) :
    ∃ t, Reachable s t ∧ ∀ z, Reachable t z → potential z ≤ potential t := by
  letI := Fintype.ofFinite (HoleState H)
  let R := Finset.univ.filter (Reachable s)
  have hs : s ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image R potential ⟨s,hs⟩
  have hst := (Finset.mem_filter.mp ht).2
  exact ⟨t,hst,fun z hz => hmax z (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hst.trans hz⟩)⟩

theorem maximal_component_imbalance {F : Finset W} (φ : PartialColouring H F)
    (e : W) (he : e ∉ F)
    (hmax : ∀ z, Reachable (make φ e he) z → potential z ≤ φ.classSquare)
    {a b : Colour} (hab : a ≠ b) (hsize : φ.classSize b ≤ φ.classSize a)
    (x : W) (hx : x ∈ φ.Bicoloured a b) :
    0 ≤ φ.imbalance a b {y | φ.SameComponent a b x y} ∧
      φ.imbalance a b {y | φ.SameComponent a b x y} ≤ φ.classSize a - φ.classSize b := by
  apply φ.propositionP7 hab (φ.component_closed a b x) _ hsize
  let ψ := φ.swap a b {y | φ.SameComponent a b x y} (φ.component_closed a b x)
  have hs : Step (make φ e he) (make ψ e he) := Step.kempe φ e he a b hab x hx
  have hr : Reachable (make φ e he) (make ψ e he) := Relation.ReflTransGen.single hs
  exact hmax (make ψ e he) hr

end HoleState
end Se20Insertion
