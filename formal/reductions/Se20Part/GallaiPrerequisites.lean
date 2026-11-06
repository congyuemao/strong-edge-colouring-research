import Se20Part.Greedy
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-! The small critical-list interface used by the copied Gallai proof.
These definitions and proofs are extracted from the sister project's
CriticalStructure, HoleMoves, Counting and LowDegree modules. -/
noncomputable section
open scoped Classical
namespace Se20Part

def CriticalSet {W : Type*} [DecidableEq W] (H : SimpleGraph W) (F : Finset W) : Prop :=
  ¬ Nonempty (PartialColouring H F) ∧
    ∀ e ∈ F, Nonempty (PartialColouring H (F.erase e))

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def restrict (φ : PartialColouring H F) (F' : Finset W) (h : F' ⊆ F) : PartialColouring H F' where
  colour := φ.colour
  proper := by
    intro x y hx hy hxy
    exact φ.proper (h hx) (h hy) hxy

def colouredNeighbours (φ : PartialColouring H F) (e : W) : Finset W := F.filter (H.Adj e)

def available (φ : PartialColouring H F) (v : W) : Finset Colour :=
  Finset.univ.filter (φ.Free v)

theorem available_card (φ : PartialColouring H F) (v : W) :
    20 ≤ (φ.available v).card + (φ.colouredNeighbours v).card := by
  have heq : φ.available v = Finset.univ \ (φ.colouredNeighbours v).image φ.colour := by
    ext c; simp [available, Free, Neighbour, colouredNeighbours, and_assoc]
  have hparts := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour)
    ((φ.colouredNeighbours v).image φ.colour)
  rw [← heq, Finset.univ_inter] at hparts
  have hi := Finset.card_image_le (s := φ.colouredNeighbours v) (f := φ.colour)
  have hc : (Finset.univ : Finset Colour).card = 20 := rfl
  omega

end PartialColouring
end Se20Part
