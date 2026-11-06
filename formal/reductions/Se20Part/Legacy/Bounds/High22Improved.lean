module

public import Se20Part.Legacy.Bounds.High22SupportSize
public import Se20Part.Legacy.Bounds.LowSupportGeometry

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The final high22 boundary: both possible positive-defect distributions
force too many internal original edges and too few available selected edges. -/
theorem high22_subcubic_seventeen_impossible
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 17) : False := by
  let S := selectedSupport G Q
  let L := selectedLowVertices G Q
  let H := selectedLeafVertices G Q
  let w := selectedDefect G Q
  let D := ∑ x ∈ S, w x
  let E := ∑ x ∈ S, w x ^ 2
  let A := ∑ x ∈ S, w x * ∑ y ∈ G.neighborFinset x, w y
  let W := ∑ x ∈ S, w x * (selectedCoverEdges G Q x).card
  have hreg : ∀ x ∈ S, G.degree x = 4 ∧ G.neighborFinset x ⊆ S :=
    fun x hx => subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx
  have hS : S.card = 13 := high22_subcubic_seventeen_support_card_thirteen G hΔ Q hQ h22 hd hq
  have hhand := selected_defect_sum_handshake G Q hd
  change D + 2 * Q.card = 3 * S.card at hhand
  have hD : D = 5 := by omega
  obtain ⟨hlin, hsq⟩ := selected_defect_counts G Q
  change D = L.card + H.card at hlin
  change E = L.card + 3 * H.card at hsq
  have hi := subcubic_seventeen_weighted_identity G hΔ Q hQ hd hq
  change W + A = 9 * D + E at hi
  have hb : W ≤ 34 := subcubic_seventeen_defect_weighted_budget G hΔ Q hQ hd hq
  have hcomp : A + E ≤ D ^ 2 := closed_weight_square_complete_bound G S
    (fun x hx => (hreg x hx).2) w
  have hcomp' := hcomp
  rw [hD] at hcomp'
  norm_num at hcomp'
  have hH : H.card ≤ 1 := by omega
  have hLS : L ⊆ S := filter_subset _ _
  have hLsum : (∑ x ∈ L, w x) = 5 := by
    have heq : (∑ x ∈ L, w x) = ∑ x ∈ S, w x := by
      apply sum_subset hLS
      intro x hx hnx
      have hn : ¬ 0 < w x := fun h => hnx (mem_filter.mpr ⟨hx, h⟩)
      omega
    exact heq.trans hD
  by_cases hH0 : H.card = 0
  · have hL5 : L.card = 5 := by omega
    have hw : ∀ x ∈ S, w x = if x ∈ L then 1 else 0 := by
      intro x hx
      have hw2 : w x ≤ 2 := selectedDefect_le_two G Q hx
      have hn2 : w x ≠ 2 := by
        intro h
        have hp : 0 < H.card := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, h⟩⟩
        omega
      by_cases hxL : x ∈ L
      · have hp : 0 < w x := (mem_filter.mp hxL).2
        simp only [hxL, ite_true]
        omega
      · have hn : ¬ 0 < w x := fun h => hxL (mem_filter.mpr ⟨hx, h⟩)
        simp only [hxL, ite_false]
        omega
    have hAeq : A = ∑ x ∈ L, (L.filter (G.Adj x)).card :=
      closed_unit_weight_adj_eq_internal_sum G S L hLS (fun x hx => (hreg x hx).2) w hw
    have hAlow : 16 ≤ ∑ x ∈ L, (L.filter (G.Adj x)).card := by omega
    have hno : ∀ e ∈ Q, ¬ ∀ x ∈ e.val, x ∈ L := by
      intro e heQ hall
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      have hu := hall u (hev ▸ Sym2.mem_mk_left u v)
      have hv := hall v (hev ▸ Sym2.mem_mk_right u v)
      have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.property)
      have hsmall := internal_degree_sum_le_fourteen_of_triangle_free_edge G L (by omega) hu hv huv
        (fun z _ huz hvz => subcubic_large_no_triangle_on_selected_edge G hΔ Q hQ hd
          (by omega) e heQ hev.symm huz hvz)
      omega
    have hupper := no_selected_inside_internal_degree_bound G hΔ Q hd L hno
    change _ ≤ L.card + ∑ x ∈ L, w x at hupper
    omega
  · have hH1 : H.card = 1 := by omega
    have hL4 : L.card = 4 := by omega
    have hE : E = 7 := by omega
    have heq : A + E = D ^ 2 := by rw [hD]; norm_num; omega
    have hclique : G.IsClique (L : Set V) := positive_weight_clique_of_complete_equality G S
      (fun x hx => (hreg x hx).2) w heq
    have hno := no_selected_inside_clique_of_card_ge_three G hΔ Q hQ hd (by omega) L hclique (by omega)
    have hupper := no_selected_inside_internal_degree_bound G hΔ Q hd L hno
    have hsum : (∑ x ∈ L, (L.filter (G.Adj x)).card) = 12 := by
      calc
        _ = ∑ _x ∈ L, 3 := by
          apply sum_congr rfl
          intro x hx
          have hf : L.filter (G.Adj x) = L.erase x := by
            ext y
            exact ⟨fun h => mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm, (mem_filter.mp h).1⟩,
              fun h => mem_filter.mpr ⟨(mem_erase.mp h).2, hclique hx (mem_erase.mp h).2 (mem_erase.mp h).1.symm⟩⟩
          rw [hf]
          have hc := card_erase_add_one hx
          omega
        _ = _ := by simp [hL4]
    change _ ≤ L.card + ∑ x ∈ L, w x at hupper
    omega

theorem high22_clique_card_le_sixteen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) : Q.card ≤ 16 := by
  have hc := clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ hd
  by_contra hn
  exact high22_subcubic_seventeen_impossible G hΔ Q hQ h22 hd (by omega)

/-- Unconditional stronger high22 threshold in the full original graph. -/
theorem high22_clique_card_le_sixteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) : Q.card ≤ 16 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high22_clique_card_le_sixteen_of_root_four G hΔ Q hQ h22 r
      (by rw [rootLabels_card]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  exact high22_clique_card_le_sixteen_of_support_degree_le_three G hΔ Q hQ h22 hthree

end Se20Part.Legacy
