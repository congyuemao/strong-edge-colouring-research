import Se20Insertion.Counting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace ComponentBounds
variable {X : Type*} [Fintype X] (H : SimpleGraph X)

theorem sum_component_sizes :
    ∑ c : H.ConnectedComponent, Nat.card c.supp = Nat.card X := by
  let e : (Σ c : H.ConnectedComponent, c.supp) ≃ X :=
    { toFun := fun p => p.2.val
      invFun := fun x => ⟨H.connectedComponentMk x, ⟨x, rfl⟩⟩
      left_inv := by
        rintro ⟨c, x, hx⟩
        change H.connectedComponentMk x = c at hx
        subst c
        rfl
      right_inv := fun _ => rfl }
  simpa only [Nat.card_sigma] using Nat.card_congr e

theorem sum_component_edges_le :
    ∑ c : H.ConnectedComponent, Nat.card c.toSimpleGraph.edgeSet ≤ Nat.card H.edgeSet := by
  let f : (Σ c : H.ConnectedComponent, c.toSimpleGraph.edgeSet) → H.edgeSet :=
    fun p => p.1.toSimpleGraph_hom.mapEdgeSet p.2
  have hf : Function.Injective f := by
    rintro ⟨c,e⟩ ⟨d,k⟩ heq
    let v := e.val.out.1
    have hv : v ∈ e.val := Sym2.out_fst_mem e.val
    have him : v.val ∈ (c.toSimpleGraph_hom.mapEdgeSet e).val :=
      Sym2.mem_map.mpr ⟨v, hv, rfl⟩
    change c.toSimpleGraph_hom.mapEdgeSet e = d.toSimpleGraph_hom.mapEdgeSet k at heq
    rw [heq] at him
    obtain ⟨w, _hw, hwv⟩ := Sym2.mem_map.mp him
    have hcd : c = d := SimpleGraph.ConnectedComponent.eq_of_common_vertex v.prop (hwv ▸ w.prop)
    subst d
    have hek : e = k := Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val heq))
    subst k
    rfl
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_sigma] using hh

/-- The elementary `vertices ≤ edges + components` bound, with isolated
vertices counted as components. -/
theorem vertices_le_edges_add_components :
    Nat.card X ≤ Nat.card H.edgeSet + Nat.card H.ConnectedComponent := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset H.ConnectedComponent))
    (fun c _ => c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one)
  have hv := sum_component_sizes H
  have he := sum_component_edges_le H
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card] at hh
  change (∑ c : H.ConnectedComponent, Nat.card c.supp) ≤ _ at hh
  rw [hv] at hh
  omega

def smallComponents (k : ℕ) : ℕ :=
  Nat.card {c : H.ConnectedComponent // Nat.card c.supp = k}

theorem small_components_mass :
    3 * Nat.card H.ConnectedComponent ≤ Nat.card X +
      2 * smallComponents H 1 + smallComponents H 2 := by
  have hp : ∀ c : H.ConnectedComponent, 0 < Nat.card c.supp := by
    intro c
    let : Nonempty c.supp := c.nonempty_supp.to_subtype
    exact Nat.card_pos
  have hh : ∀ c : H.ConnectedComponent,
      3 ≤ Nat.card c.supp + (if Nat.card c.supp = 1 then 2 else 0) +
        (if Nat.card c.supp = 2 then 1 else 0) := by
    intro c
    have := hp c
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset H.ConnectedComponent)) => hh c)
  have h1 : (∑ c : H.ConnectedComponent, if Nat.card c.supp = 1 then 2 else 0) =
      2 * smallComponents H 1 := by
    simp [smallComponents, Nat.card_eq_fintype_card, Fintype.card_subtype,
      ← Finset.sum_filter, Finset.sum_const, mul_comm]
  have h2 : (∑ c : H.ConnectedComponent, if Nat.card c.supp = 2 then 1 else 0) =
      smallComponents H 2 := by
    simp [smallComponents, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card] at hsum
  rw [sum_component_sizes, h1, h2] at hsum
  omega

end ComponentBounds
end Se20Insertion
