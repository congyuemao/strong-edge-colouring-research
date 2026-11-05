module

public import Se20Part.Legacy.Bounds.High22Subcubic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem clique_card_le_nineteen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3) : Q.card ≤ 19 := by
  by_cases hQempty : Q = ∅
  · simp [hQempty]
  obtain ⟨e, heQ⟩ := nonempty_iff_ne_empty.mpr hQempty
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := clique_card_le_one_add_incidence_sum G Q hQ e heQ he.symm
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hQdeg w)
  have hcard := endpointNeighbourCover_card_le_six G huv hΔ
  simp only [sum_const, smul_eq_mul] at hs
  omega

/-- A hypothetical nineteen-edge subcubic clique saturates every local cover. -/
theorem subcubic_nineteen_cover_saturated
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3) (h19 : Q.card = 19)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    (endpointNeighbourCover G u v).card = 6 ∧
      ∀ w ∈ endpointNeighbourCover G u v, (edgeIncidences G Q w).card = 3 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := clique_card_le_one_add_incidence_sum G Q hQ e heQ he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hQdeg w)
  have hcard := endpointNeighbourCover_card_le_six G huv hΔ
  simp only [sum_const, smul_eq_mul] at hs
  refine ⟨by omega, ?_⟩
  intro w hw
  have heq := sum_erase_add (endpointNeighbourCover G u v)
    (fun x => (edgeIncidences G Q x).card) hw
  have hce := card_erase_add_one hw
  have hse := sum_le_sum (s := (endpointNeighbourCover G u v).erase w)
    (fun x _ => hQdeg x)
  have hd := hQdeg w
  simp only [sum_const, smul_eq_mul] at hse
  omega

theorem subcubic_nineteen_supported_degree_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3) (h19 : Q.card = 19)
    {x : V} (hx : 0 < (edgeIncidences G Q x).card) :
    (edgeIncidences G Q x).card = 3 := by
  obtain ⟨e, he⟩ := card_pos.mp hx
  obtain ⟨heQ, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
  obtain ⟨hcard, hsat⟩ := subcubic_nineteen_cover_saturated G hΔ Q hQ hQdeg h19 e heQ hey
  have hcx := card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy)
  have hcy := card_erase_add_one ((G.mem_neighborFinset y x).mpr hxy.symm)
  have hcu := card_union_le ((G.neighborFinset x).erase y) ((G.neighborFinset y).erase x)
  have hdy := hΔ y
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcx hcy
  have hpos : 0 < ((G.neighborFinset x).erase y).card := by
    dsimp [endpointNeighbourCover] at hcard
    omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  have hda := hsat a (mem_union_left _ ha)
  have hlabels : 1 < (rootLabels G Q a).card := by rw [rootLabels_card, hda]; omega
  obtain ⟨b, hb, hbx⟩ := exists_mem_ne hlabels x
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp hb
  have hax := ((G.mem_neighborFinset x a).mp (mem_erase.mp ha).2).symm
  exact (subcubic_nineteen_cover_saturated G hΔ Q hQ hQdeg h19 f hfQ hf).2 x
    (mem_union_left _ (mem_erase.mpr ⟨hbx.symm, (G.mem_neighborFinset a x).mpr hax⟩))

/-- Threshold-free bound sufficient for the high21 subcubic branch.
The equality case at nineteen would make every supported degree three,
contradicting the handshake sum of thirty-eight. -/
theorem clique_card_le_eighteen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3) : Q.card ≤ 18 := by
  by_contra hn
  have hc := clique_card_le_nineteen_of_support_degree_le_three G hΔ Q hQ hQdeg
  have h19 : Q.card = 19 := by omega
  have hdiv : 3 ∣ ∑ x : V, (edgeIncidences G Q x).card := by
    apply Finset.dvd_sum
    intro x _
    by_cases hx : (edgeIncidences G Q x).card = 0
    · simp only [hx, dvd_zero]
    · rw [subcubic_nineteen_supported_degree_three G hΔ Q hQ hQdeg h19 (by omega)]
  have hi := incidence_sum_eq_meeting_add_inside G Q (univ : Finset V)
  have hin : edgesInside G Q (univ : Finset V) = Q := by simp [edgesInside]
  have hmeet : edgesMeeting G Q (univ : Finset V) = Q := by
    apply filter_eq_self.mpr
    intro e _
    obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    exact ⟨u, mem_univ _, he ▸ Sym2.mem_mk_left u v⟩
  rw [hin, hmeet, h19] at hi
  rw [hi] at hdiv
  norm_num at hdiv

end Se20Part.Legacy
