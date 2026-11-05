import Se20Part.Definitions
import Mathlib.Order.Preorder.Finite

noncomputable section
open scoped Classical
namespace Se20Part

def Independent {W : Type*} (H : SimpleGraph W) (I : Set W) : Prop :=
  ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ I → ¬ H.Adj x y

/-- The maximal-extension argument used in step 4; no unproved graph theorem is assumed. -/
theorem independent_extension {W : Type*} [Fintype W] (H : SimpleGraph W)
    (A J : Set W) (hJA : J ⊆ A) (hJ : Independent H J) :
    ∃ I : Set W, J ⊆ I ∧ I ⊆ A ∧ Independent H I ∧
      ∀ x ∈ A, x ∉ I → ∃ y ∈ I, H.Adj x y := by
  let S : Set (Set W) := {I | J ⊆ I ∧ I ⊆ A ∧ Independent H I}
  obtain ⟨I, hI⟩ := S.toFinite.exists_maximal ⟨J, Set.Subset.rfl, hJA, hJ⟩
  refine ⟨I, hI.1.1, hI.1.2.1, hI.1.2.2, ?_⟩
  intro x hx hxi
  by_contra hn
  have hxn : ∀ y ∈ I, ¬ H.Adj x y := by simpa using hn
  have hnew : insert x I ∈ S := by
    refine ⟨hI.1.1.trans (Set.subset_insert _ _), ?_, ?_⟩
    · exact Set.insert_subset hx hI.1.2.1
    · intro y hy z hz hyz
      rcases hy with rfl | hy <;> rcases hz with rfl | hz
      · exact H.irrefl hyz
      · exact hxn z hz hyz
      · exact hxn y hy hyz.symm
      · exact hI.1.2.2 hy hz hyz
  exact hxi (hI.mem_of_prop_insert hnew)

theorem induced_degree_le {W : Type*} [Fintype W] (H : SimpleGraph W)
    (K : Set W) (v : K) :
    Nat.card ((H.induce K).neighborSet v) ≤ Nat.card (H.neighborSet v.val) := by
  let f : (H.induce K).neighborSet v → H.neighborSet v.val :=
    fun w => ⟨w.val.val, w.property⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : H.neighborSet v.val => x.val) h))
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

theorem induced_degree_lt_of_removed_neighbor {W : Type*} [Fintype W]
    (H : SimpleGraph W) (K : Set W) (v : K) {w : W}
    (hw : w ∉ K) (hvw : H.Adj v.val w) :
    Nat.card ((H.induce K).neighborSet v) < Nat.card (H.neighborSet v.val) := by
  let f : (H.induce K).neighborSet v → H.neighborSet v.val :=
    fun w => ⟨w.val.val, w.property⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : H.neighborSet v.val => x.val) h))
  have hn : (⟨w,hvw⟩ : H.neighborSet v.val) ∉ Set.range f := by
    rintro ⟨a, ha⟩
    have he : a.val.val = w := congrArg (fun x : H.neighborSet v.val => x.val) ha
    exact hw (he ▸ a.val.property)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_of_notMem f hf hn

/-- Steps 4–5 as an abstract graph lemma. `N` is the forbidden region and `J` its seed dominators. -/
theorem domination_reduces_degree {W : Type*} [Fintype W] (H : SimpleGraph W)
    (N J : Set W) {d : ℕ} (hd : DegreeLE H (d+1)) (hJN : J ⊆ Nᶜ)
    (hJ : Independent H J)
    (hdom : ∀ x ∈ N, Nat.card (H.neighborSet x) = d+1 → ∃ y ∈ J, H.Adj x y) :
    ∃ I : Set W, J ⊆ I ∧ I ⊆ Nᶜ ∧ Independent H I ∧ DegreeLE (H.induce Iᶜ) d := by
  obtain ⟨I, hJI, hIN, hI, hmax⟩ := independent_extension H Nᶜ J hJN hJ
  refine ⟨I, hJI, hIN, hI, ?_⟩
  intro x
  by_cases hlow : Nat.card (H.neighborSet x.val) ≤ d
  · exact (induced_degree_le H Iᶜ x).trans hlow
  · have heq : Nat.card (H.neighborSet x.val) = d+1 := by have := hd x.val; omega
    have hex : ∃ y ∈ I, H.Adj x.val y := by
      by_cases hxn : x.val ∈ N
      · obtain ⟨y, hy, hxy⟩ := hdom x.val hxn heq
        exact ⟨y, hJI hy, hxy⟩
      · exact hmax x.val hxn x.property
    obtain ⟨y, hy, hxy⟩ := hex
    have hlt := induced_degree_lt_of_removed_neighbor H Iᶜ x (by simpa using hy) hxy
    omega

/-- The independent-union check in Theorem B, step 5. -/
theorem independent_union {W : Type*} {H : SimpleGraph W} {D I : Set W}
    (hD : Independent H D) (hI : Independent H I)
    (hcross : ∀ x ∈ D, ∀ y ∈ I, ¬ H.Adj x y) : Independent H (D ∪ I) := by
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hD hx hy hxy
  · exact hcross x hx y hy hxy
  · exact hcross y hy x hx hxy.symm
  · exact hI hx hy hxy

end Se20Part
