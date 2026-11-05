import Se20Part.Definitions
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical BigOperators
namespace Se20Part

def Independent {W : Type*} (H : SimpleGraph W) (M : Finset W) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ¬ H.Adj x y

/-- Independence number of the fixed ambient graph restricted to F. -/
def packingRank {W : Type*} (H : SimpleGraph W) (F : Finset W) : ℕ :=
  F.powerset.sup (fun M => if Independent H M then M.card else 0)

theorem independent_le_packingRank {W : Type*} (H : SimpleGraph W) (F M : Finset W)
    (hMF : M ⊆ F) (hM : Independent H M) : M.card ≤ packingRank H F := by
  have h := Finset.le_sup (f := fun M => if Independent H M then M.card else 0)
    (Finset.mem_powerset.mpr hMF)
  simpa only [packingRank, ite_eq_left hM] using h

namespace Packing
variable {W : Type*} (H : SimpleGraph W) (F : Finset W)

/-- A family of genuine disjoint, mutually nonadjacent, twenty-vertex blocks.
Completeness of the individual blocks is not needed for the 18⇒19 implication. -/
structure TwentyBlocks where
  blocks : Finset (Finset W)
  card_twenty : ∀ B ∈ blocks, B.card = 20
  disjoint : (blocks : Set (Finset W)).PairwiseDisjoint id
  separated : ∀ B ∈ blocks, ∀ D ∈ blocks, B ≠ D →
    ∀ x ∈ B, ∀ y ∈ D, ¬ H.Adj x y

def tau (B : TwentyBlocks H) : ℕ := ∑ S ∈ B.blocks, ((F ∩ S).card - 18)
def fullCount (B : TwentyBlocks H) : ℕ := (B.blocks.filter (fun S => (F ∩ S).card = 20)).card

/-- The non-certificate counting argument in item 5.7. -/
theorem tau_le_rank_add_full (B : TwentyBlocks H) :
    tau H F B ≤ packingRank H F + fullCount H F B := by
  let A := B.blocks.filter (fun S => 18 < (F ∩ S).card)
  have nonempty (S : A) : (F ∩ S.val).Nonempty :=
    Finset.card_pos.mp (by have := (Finset.mem_filter.mp S.prop).2; omega)
  let r : A → W := fun S => (nonempty S).choose
  have hr (S : A) : r S ∈ F ∩ S.val := (nonempty S).choose_spec
  have hinj : Function.Injective r := by
    intro S T heq
    apply Subtype.ext
    by_contra hST
    have hdis := B.disjoint (Finset.mem_filter.mp S.prop).1 (Finset.mem_filter.mp T.prop).1 hST
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp (hr S)).2
      (heq.symm ▸ (Finset.mem_inter.mp (hr T)).2)
  let M := Finset.univ.image r
  have hMF : M ⊆ F := by
    intro x hx
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_inter.mp (hr S)).1
  have hM : Independent H M := by
    intro x hx y hy
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hy
    by_cases hST : S = T
    · subst T; exact fun h => H.irrefl h
    · apply B.separated S.val (Finset.mem_filter.mp S.prop).1
        T.val (Finset.mem_filter.mp T.prop).1
        (fun h => hST (Subtype.ext h)) _ (Finset.mem_inter.mp (hr S)).2
        _ (Finset.mem_inter.mp (hr T)).2
  have hA : A.card ≤ packingRank H F := by
    have h := independent_le_packingRank H F M hMF hM
    simpa [M, Finset.card_image_of_injective _ hinj] using h
  have hpoint (S : Finset W) (hS : S ∈ B.blocks) :
      (F ∩ S).card - 18 ≤ (if 18 < (F ∩ S).card then 1 else 0) +
        (if (F ∩ S).card = 20 then 1 else 0) := by
    have hle : (F ∩ S).card ≤ 20 :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq (B.card_twenty S hS)
    split_ifs <;> omega
  have hs := Finset.sum_le_sum hpoint
  have he : (∑ S ∈ B.blocks, ((if 18 < (F ∩ S).card then 1 else 0) +
      (if (F ∩ S).card = 20 then 1 else 0))) = A.card + fullCount H F B := by
    simp [Finset.sum_add_distrib, A, fullCount]
  rw [he] at hs
  exact hs.trans (Nat.add_le_add_right hA _)

theorem eighteen_implies_nineteen (B : TwentyBlocks H)
    (h18 : F.card ≤ 18 * packingRank H F + tau H F B) :
    F.card ≤ 19 * packingRank H F + fullCount H F B := by
  have := tau_le_rank_add_full H F B
  omega

end Packing

def PentagonDouble : SimpleGraph (Fin 5 × Fin 2) :=
  (SimpleGraph.cycleGraph 5).comap Prod.fst

def NoPentagonDoubleComponent {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ C : G.ConnectedComponent, IsEmpty ((G.induce C.supp) ≃g PentagonDouble)

/-- Cited Joos/Nguyen vertex bound, in exactly the case used for item 5.6.
This is a proposition parameter, not a new axiom. -/
def JoosNguyen : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G →
    (∀ v, ∃ w, G.Adj v w) → NoPentagonDoubleComponent G →
    Fintype.card V ≤ 9 * packingRank (L2 G) Finset.univ

/-- Item 5.6 for the full edge set, with no isolated vertices and no tight
component. The extensions to isolated vertices and tight components are separate. -/
theorem full_edge_eighteen_of_joos (hJoos : JoosNguyen)
    {V : Type} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G)
    (hiso : ∀ v, ∃ w, G.Adj v w) (htight : NoPentagonDoubleComponent G) :
    Fintype.card G.edgeSet ≤ 18 * packingRank (L2 G) Finset.univ := by
  have hj := hJoos V G hΔ hiso htight
  have hs : (∑ v, G.degree v) ≤ 4 * Fintype.card V := by
    calc
      _ ≤ ∑ _v : V, 4 := Finset.sum_le_sum (fun v _ => hΔ v)
      _ = _ := by simp [Nat.mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges, ← G.card_edgeSet] at hs
  omega

end Se20Part
