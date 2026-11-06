import Se20Insertion.P6Core
import Se20Insertion.PotentialReachability

noncomputable section
open scoped Classical
namespace Se20Insertion.P6.Pattern
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

/-- The operations permitted in P6: donors outside the fixed pair, and
swaps of that pair on any union of complete Kempe components. -/
inductive FixedPairStep (a b : Colour) : HoleState (L2 G) → HoleState (L2 G) → Prop
  | hole {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
      {h f : G.edgeSet} {p : Colour} (hh : h ∉ F) (hs : φ.Single h p f)
      (hp : p ∉ ({a,b} : Finset Colour)) :
      FixedPairStep a b (HoleState.make φ h hh)
        (HoleState.make (φ.holeMove hs) f (by simp [hs.1.2.1.ne.symm]))
  | swap {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
      (h : G.edgeSet) (hh : h ∉ F) (S : Set G.edgeSet) (hS : φ.KempeClosed a b S) :
      FixedPairStep a b (HoleState.make φ h hh)
        (HoleState.make (φ.swap a b S hS) h hh)

theorem fixedPairStep_preserves {a b : Colour} {s t : HoleState (L2 G)}
    (hc : P.PairClasses s.val.1.2 a b) (hst : FixedPairStep a b s t) :
    P.PairClasses t.val.1.2 a b := by
  cases hst with
  | hole φ hh hs hp => exact PairClasses.holeMove P hc hh hs hp
  | swap φ h hh S hS => exact PairClasses.swap P hc hS

/-- Every finite permitted route leaves the fixed pair blocked at the
actual current hole, even when the swaps and hole moves are interleaved. -/
theorem fixedPairRoute_blocked {a b : Colour} (hab : a ≠ b)
    {s t : HoleState (L2 G)} (hc : P.PairClasses s.val.1.2 a b)
    (hst : Relation.ReflTransGen (FixedPairStep a b) s t) :
    ¬ t.val.1.2.Free t.val.2 a ∧ ¬ t.val.1.2.Free t.val.2 b ∧
      ¬ t.val.1.2.Separable t.val.2 a b := by
  have ht : P.PairClasses t.val.1.2 a b := by
    induction hst with
    | refl => exact hc
    | tail _ hstep ih => exact P.fixedPairStep_preserves ih hstep
  exact P.uncoloured_pair_blocked t.val.1.2 hab ht t.prop

end Se20Insertion.P6.Pattern
