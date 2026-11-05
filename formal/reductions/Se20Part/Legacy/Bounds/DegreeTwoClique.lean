module

public import Se20Part.Legacy.Bounds.SubcubicEighteen

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Counting within a vertex set keeps every original edge between its vertices.
No conflict graph is changed in any of the following lemmas. -/
theorem restricted_incidence_card_le
    (Q : Finset G.edgeSet) (P : Finset V)
    (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P) (x : V) :
    (edgeIncidences G Q x).card ≤ (G.neighborFinset x ∩ P).card := by
  rw [← rootLabels_card]
  apply card_le_card
  intro y hy
  obtain ⟨hyN, e, heQ, he⟩ := mem_filter.mp hy
  exact mem_inter.mpr ⟨hyN, hP e heQ y (he.symm ▸ Sym2.mem_mk_right x y)⟩

theorem restricted_cover_card_le_two
    (P : Finset V) (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2)
    {u v : V} (hu : u ∈ P) (hv : v ∈ P) (huv : G.Adj u v) :
    (endpointNeighbourCover G u v ∩ P).card ≤ 2 := by
  have heq : endpointNeighbourCover G u v ∩ P =
      ((G.neighborFinset u ∩ P).erase v) ∪ ((G.neighborFinset v ∩ P).erase u) := by
    ext w
    simp only [endpointNeighbourCover, mem_inter, mem_union, mem_erase]
    tauto
  have hcu := card_erase_add_one (mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hv⟩)
  have hcv := card_erase_add_one (mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr huv.symm, hu⟩)
  have hdu := hd u hu
  have hdv := hd v hv
  rw [heq]
  have hc := card_union_le ((G.neighborFinset u ∩ P).erase v) ((G.neighborFinset v ∩ P).erase u)
  omega

theorem clique_card_le_one_add_restricted_incidence_sum
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    Q.card ≤ 1 + ∑ w ∈ endpointNeighbourCover G u v ∩ P, (edgeIncidences G Q w).card := by
  have hs : Q.erase e ⊆ edgesMeeting G Q (endpointNeighbourCover G u v ∩ P) := by
    intro f hf
    obtain ⟨hne, hfQ⟩ := mem_erase.mp hf
    obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he (hQ heQ hfQ hne.symm)
    exact mem_filter.mpr ⟨hfQ, w, mem_inter.mpr ⟨hw, hP f hfQ w hwf⟩, hwf⟩
  have hc := card_le_card hs
  have hsum := incidence_sum_eq_meeting_add_inside G Q (endpointNeighbourCover G u v ∩ P)
  have hec := card_erase_add_one heQ
  omega

theorem degree_two_clique_card_le_five
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2) : Q.card ≤ 5 := by
  by_cases hQempty : Q = ∅
  · simp [hQempty]
  obtain ⟨e, heQ⟩ := nonempty_iff_ne_empty.mpr hQempty
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hu := hP e heQ u (he ▸ Sym2.mem_mk_left u v)
  have hv := hP e heQ v (he ▸ Sym2.mem_mk_right u v)
  have hc := clique_card_le_one_add_restricted_incidence_sum G Q hQ P hP e heQ he.symm
  have hs := sum_le_sum (s := endpointNeighbourCover G u v ∩ P) (fun w hw =>
    (restricted_incidence_card_le G Q P hP w).trans (hd w (mem_inter.mp hw).2))
  have hcard := restricted_cover_card_le_two G P hd hu hv (G.mem_edgeSet.mp (he ▸ e.property))
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem degree_two_five_cover_saturated
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2) (h5 : Q.card = 5)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    (endpointNeighbourCover G u v ∩ P).card = 2 ∧
      ∀ w ∈ endpointNeighbourCover G u v ∩ P, (edgeIncidences G Q w).card = 2 := by
  have hu := hP e heQ u (he.symm ▸ Sym2.mem_mk_left u v)
  have hv := hP e heQ v (he.symm ▸ Sym2.mem_mk_right u v)
  have hc := clique_card_le_one_add_restricted_incidence_sum G Q hQ P hP e heQ he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v ∩ P) (fun w hw =>
    (restricted_incidence_card_le G Q P hP w).trans (hd w (mem_inter.mp hw).2))
  have hcard := restricted_cover_card_le_two G P hd hu hv (G.mem_edgeSet.mp (he ▸ e.property))
  simp only [sum_const, smul_eq_mul] at hs
  refine ⟨by omega, ?_⟩
  intro w hw
  have heq := sum_erase_add (endpointNeighbourCover G u v ∩ P)
    (fun x => (edgeIncidences G Q x).card) hw
  have hce := card_erase_add_one hw
  have hse := sum_le_sum (s := (endpointNeighbourCover G u v ∩ P).erase w)
    (fun x hx => (restricted_incidence_card_le G Q P hP x).trans
      (hd x (mem_inter.mp (mem_erase.mp hx).2).2))
  have hdw := (restricted_incidence_card_le G Q P hP w).trans (hd w (mem_inter.mp hw).2)
  simp only [sum_const, smul_eq_mul] at hse
  omega

theorem degree_two_five_supported_degree_two
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2) (h5 : Q.card = 5)
    {x : V} (hx : 0 < (edgeIncidences G Q x).card) :
    (edgeIncidences G Q x).card = 2 := by
  obtain ⟨e, he⟩ := card_pos.mp hx
  obtain ⟨heQ, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
  have hxP := hP e heQ x hxe
  have hyP := hP e heQ y (hey.symm ▸ Sym2.mem_mk_right x y)
  obtain ⟨hcard, hsat⟩ := degree_two_five_cover_saturated G Q hQ P hP hd h5 e heQ hey
  have hcy := card_erase_add_one (mem_inter.mpr ⟨(G.mem_neighborFinset y x).mpr hxy.symm, hxP⟩)
  have hdy := hd y hyP
  have heq : endpointNeighbourCover G x y ∩ P =
      ((G.neighborFinset x ∩ P).erase y) ∪ ((G.neighborFinset y ∩ P).erase x) := by
    ext w
    simp only [endpointNeighbourCover, mem_inter, mem_union, mem_erase]
    tauto
  have hcu := card_union_le ((G.neighborFinset x ∩ P).erase y) ((G.neighborFinset y ∩ P).erase x)
  have hpos : 0 < ((G.neighborFinset x ∩ P).erase y).card := by rw [heq] at hcard; omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  have haC : a ∈ endpointNeighbourCover G x y ∩ P := heq.symm ▸ mem_union_left _ ha
  have hda := hsat a haC
  have hlabels : 1 < (rootLabels G Q a).card := by rw [rootLabels_card, hda]; omega
  obtain ⟨b, hb, hbx⟩ := exists_mem_ne hlabels x
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp hb
  have hax := ((G.mem_neighborFinset x a).mp (mem_inter.mp (mem_erase.mp ha).2).1).symm
  exact (degree_two_five_cover_saturated G Q hQ P hP hd h5 f hfQ hf).2 x
    (mem_inter.mpr ⟨mem_union_left _ (mem_erase.mpr
      ⟨hbx.symm, (G.mem_neighborFinset a x).mpr hax⟩), hxP⟩)

/-- A selected bipartition suffices; original witness edges inside P are
retained and are not required to respect the bipartition. -/
theorem degree_two_clique_card_le_four_of_selected_bipartition
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2)
    (L : Finset V) (hL : ∀ e ∈ Q, (L.filter (fun x => x ∈ e.val)).card = 1) :
    Q.card ≤ 4 := by
  by_contra hn
  have hc := degree_two_clique_card_le_five G Q hQ P hP hd
  have h5 : Q.card = 5 := by omega
  have hdiv : 2 ∣ ∑ x ∈ L, (edgeIncidences G Q x).card := by
    apply Finset.dvd_sum
    intro x _
    by_cases hx : (edgeIncidences G Q x).card = 0
    · simp only [hx, dvd_zero]
    · rw [degree_two_five_supported_degree_two G Q hQ P hP hd h5 (by omega)]
  have hi : (∑ x ∈ L, (edgeIncidences G Q x).card) = Q.card := by
    calc
      _ = ∑ e ∈ Q, (L.filter (fun x => x ∈ e.val)).card := by
        simp only [edgeIncidences, card_eq_sum_ones, sum_filter]
        exact sum_comm
      _ = ∑ _e ∈ Q, 1 := sum_congr rfl hL
      _ = Q.card := by simp
  rw [hi, h5] at hdiv
  norm_num at hdiv

end Se20Part.Legacy
