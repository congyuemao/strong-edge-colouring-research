module

public import Se20Part.Legacy.Bounds.High22ImprovedRoot

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Endpoints of the selected edges; ambient edges are not deleted. -/
def selectedSupport (Q : Finset G.edgeSet) : Finset V :=
  univ.filter (fun x => 0 < (edgeIncidences G Q x).card)

theorem subcubic_large_cover_card_and_degree
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    (endpointNeighbourCover G u v).card = 6 ∧
      ∀ x ∈ endpointNeighbourCover G u v, Q.card ≤ 16 + (edgeIncidences G Q x).card := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := clique_card_le_one_add_incidence_sum G Q hQ e heQ he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun x _ => hd x)
  have hb := endpointNeighbourCover_card_le_six G huv hΔ
  simp only [sum_const, smul_eq_mul] at hs
  refine ⟨by omega, ?_⟩
  intro x hx
  have hec := card_erase_add_one hx
  have heq := sum_erase_add (endpointNeighbourCover G u v) (fun y => (edgeIncidences G Q y).card) hx
  have hse := sum_le_sum (s := (endpointNeighbourCover G u v).erase x) (fun y _ => hd y)
  simp only [sum_const, smul_eq_mul] at hse
  omega

theorem subcubic_large_endpoints_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    G.degree u = 4 ∧ G.degree v = 4 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd hq e heQ he).1
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hb := card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [endpointNeighbourCover] at hc
  omega

/-- Any subcubic clique of size at least seventeen already has a closed,
four-regular support in the original graph. No high-degree threshold is used. -/
theorem subcubic_large_support_closed_regular
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    {x : V} (hx : x ∈ selectedSupport G Q) :
    G.degree x = 4 ∧ G.neighborFinset x ⊆ selectedSupport G Q := by
  obtain ⟨e, he⟩ := card_pos.mp (mem_filter.mp hx).2
  obtain ⟨heQ, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  refine ⟨(subcubic_large_endpoints_degree_four G hΔ Q hQ hd hq e heQ hey).1, ?_⟩
  intro z hz
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  by_cases hzy : z = y
  · subst z
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨heQ, hey.symm ▸ Sym2.mem_mk_right x y⟩⟩
  · have hc := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd hq e heQ hey).2 z
      (mem_union_left _ (mem_erase.mpr ⟨hzy, hz⟩))
    omega

theorem subcubic_large_no_triangle_on_selected_edge
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v))
    {w : V} (huw : G.Adj u w) (hvw : G.Adj v w) : False := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd hq e heQ he).1
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hi := card_union_add_card_inter ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hp : 0 < (((G.neighborFinset u).erase v) ∩ ((G.neighborFinset v).erase u)).card :=
    card_pos.mpr ⟨w, mem_inter.mpr
      ⟨mem_erase.mpr ⟨hvw.ne.symm, (G.mem_neighborFinset u w).mpr huw⟩,
       mem_erase.mpr ⟨huw.ne.symm, (G.mem_neighborFinset v w).mpr hvw⟩⟩⟩
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [endpointNeighbourCover] at hc
  omega

theorem subcubic_large_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb hab habG
  change G.Adj r a at ha
  change G.Adj r b at hb
  have hnot (x : V) (hx : x ∈ rootLabels G Q r) : x ≠ a ∧ x ≠ b := by
    obtain ⟨_, e, heQ, he⟩ := mem_filter.mp hx
    constructor
    · intro hxa
      exact subcubic_large_no_triangle_on_selected_edge G hΔ Q hQ hd hq e heQ
        (by simpa only [hxa] using he) hb habG
    · intro hxb
      exact subcubic_large_no_triangle_on_selected_edge G hΔ Q hQ hd hq e heQ
        (by simpa only [hxb] using he) ha habG.symm
  have hs : rootLabels G Q r ⊆ ((G.neighborFinset r).erase a).erase b := by
    intro x hx
    exact mem_erase.mpr ⟨(hnot x hx).2, mem_erase.mpr ⟨(hnot x hx).1,
      rootLabels_subset_neighbors G Q r hx⟩⟩
  have hc := card_le_card hs
  have hca := card_erase_add_one ((G.mem_neighborFinset r a).mpr ha)
  have hcb := card_erase_add_one (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset r b).mpr hb⟩)
  have hdr := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
  omega

theorem subcubic_eighteen_support_degree_ge_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18)
    {x : V} (hx : x ∈ selectedSupport G Q) : 2 ≤ (edgeIncidences G Q x).card := by
  obtain ⟨e, he⟩ := card_pos.mp (mem_filter.mp hx).2
  obtain ⟨heQ, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
  have hdx := (subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx).1
  have hec := card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hec
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < ((G.neighborFinset x).erase y).card by omega)
  have hda := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd (by omega) e heQ hey).2 a
    (mem_union_left _ ha)
  have hl : 1 < (rootLabels G Q a).card := by rw [rootLabels_card]; omega
  obtain ⟨b, hb, hbx⟩ := exists_mem_ne hl x
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp hb
  have hax := ((G.mem_neighborFinset x a).mp (mem_erase.mp ha).2).symm
  have hc := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd (by omega) f hfQ hf).2 x
    (mem_union_left _ (mem_erase.mpr ⟨hbx.symm, (G.mem_neighborFinset a x).mpr hax⟩))
  omega

/-- Selected edges covered by an original neighbour of x, excluding edges at x. -/
def selectedCoverEdges (Q : Finset G.edgeSet) (x : V) : Finset G.edgeSet :=
  (edgesMeeting G Q (G.neighborFinset x)).filter (fun e => x ∉ e.val)

theorem mem_selectedCoverEdges_iff (Q : Finset G.edgeSet) {x u v : V}
    (e : G.edgeSet) (he : e.val = s(u, v)) :
    e ∈ selectedCoverEdges G Q x ↔ e ∈ Q ∧ x ∈ endpointNeighbourCover G u v := by
  simp only [selectedCoverEdges, edgesMeeting, mem_filter, he, Sym2.mem_iff,
    endpointNeighbourCover, mem_union, mem_erase, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨heQ, a, hxa, hau | hav⟩, hn⟩
    · subst a; exact ⟨heQ, Or.inl ⟨fun h => hn (Or.inr h), hxa.symm⟩⟩
    · subst a; exact ⟨heQ, Or.inr ⟨fun h => hn (Or.inl h), hxa.symm⟩⟩
  · rintro ⟨heQ, (⟨hxv, hux⟩ | ⟨hxu, hvx⟩)⟩
    · exact ⟨⟨heQ, u, hux.symm, Or.inl rfl⟩, fun h => h.elim hux.ne.symm hxv⟩
    · exact ⟨⟨heQ, v, hvx.symm, Or.inr rfl⟩, fun h => h.elim hxu hvx.ne.symm⟩

theorem subcubic_large_selectedCoverEdges_count
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : 17 ≤ Q.card) (x : V) :
    (selectedCoverEdges G Q x).card + (edgeIncidences G Q x).card =
      ∑ a ∈ G.neighborFinset x, (edgeIncidences G Q a).card := by
  have hi : edgesInside G Q (G.neighborFinset x) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heQ, hends⟩ := mem_filter.mp he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    exact subcubic_large_no_triangle_on_selected_edge G hΔ Q hQ hd hq e heQ hev.symm
      ((G.mem_neighborFinset x u).mp (hends u (hev ▸ Sym2.mem_mk_left u v))).symm
      ((G.mem_neighborFinset x v).mp (hends v (hev ▸ Sym2.mem_mk_right u v))).symm
  have hf : (edgesMeeting G Q (G.neighborFinset x)).filter (fun e => x ∈ e.val) =
      edgeIncidences G Q x := by
    ext e
    constructor
    · intro h; exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩
    · intro h
      obtain ⟨heQ, hxe⟩ := mem_filter.mp h
      obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨heQ, y,
        (G.mem_neighborFinset x y).mpr (G.mem_edgeSet.mp (hey ▸ e.property)),
        hey.symm ▸ Sym2.mem_mk_right x y⟩, hxe⟩
  have hp := card_filter_add_card_filter_not (s := edgesMeeting G Q (G.neighborFinset x))
    (p := fun e => x ∈ e.val)
  have hc := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset x)
  rw [hi, card_empty, add_zero] at hc
  rw [hf] at hp
  change _ + (selectedCoverEdges G Q x).card = _ at hp
  omega

/-- A cover of an eighteen-edge subcubic clique contains at most one
selected-degree-two vertex. -/
theorem subcubic_eighteen_low_cover_card_le_one
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18)
    (e : G.edgeSet) (heQ : e ∈ Q) :
    ((univ.filter (fun x => (edgeIncidences G Q x).card = 2)).filter
      (fun x => e ∈ selectedCoverEdges G Q x)).card ≤ 1 := by
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  let C := endpointNeighbourCover G u v
  have hc := subcubic_large_cover_card_and_degree G hΔ Q hQ hd (by omega) e heQ hev.symm
  have heq : ∑ x ∈ C, ((edgeIncidences G Q x).card +
      if (edgeIncidences G Q x).card = 2 then 1 else 0) = 3 * C.card := by
    calc
      _ = ∑ _x ∈ C, 3 := by
        apply sum_congr rfl
        intro x hx
        have hl := hc.2 x hx
        have hu := hd x
        split_ifs <;> omega
      _ = _ := by simp [Nat.mul_comm]
  simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one] at heq
  have hs := clique_card_le_one_add_incidence_sum G Q hQ e heQ hev.symm
  have hf : ((univ.filter (fun x => (edgeIncidences G Q x).card = 2)).filter
      (fun x => e ∈ selectedCoverEdges G Q x)) =
      C.filter (fun x => (edgeIncidences G Q x).card = 2) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_selectedCoverEdges_iff G Q e hev.symm,
      heQ, true_and, C, and_comm]
  rw [hf]
  have hcard : C.card = 6 := hc.1
  change Q.card ≤ 1 + ∑ x ∈ C, (edgeIncidences G Q x).card at hs
  omega

theorem selectedCoverEdges_double_count (Q : Finset G.edgeSet) (L : Finset V) :
    (∑ x ∈ L, (selectedCoverEdges G Q x).card) =
      ∑ e ∈ Q, (L.filter (fun x => e ∈ selectedCoverEdges G Q x)).card := by
  have hf (x : V) : Q.filter (fun e => e ∈ selectedCoverEdges G Q x) = selectedCoverEdges G Q x := by
    ext e
    exact ⟨fun h => (mem_filter.mp h).2,
      fun h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1, h⟩⟩
  calc
    _ = ∑ x ∈ L, ∑ e ∈ Q, if e ∈ selectedCoverEdges G Q x then 1 else 0 := by
      apply sum_congr rfl
      intro x _
      calc
        _ = (Q.filter (fun e => e ∈ selectedCoverEdges G Q x)).card := congrArg Finset.card (hf x).symm
        _ = _ := by simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ e ∈ Q, ∑ x ∈ L, if e ∈ selectedCoverEdges G Q x then 1 else 0 := sum_comm
    _ = _ := by simp only [card_eq_sum_ones, sum_filter]

/-- Local cover counting removes all selected-degree-two vertices, without
the paper proof's global edge-pair classification. -/
theorem subcubic_eighteen_support_degree_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18)
    {x : V} (hx : x ∈ selectedSupport G Q) : (edgeIncidences G Q x).card = 3 := by
  let L := univ.filter (fun y => (edgeIncidences G Q y).card = 2)
  have hb : (∑ y ∈ L, (selectedCoverEdges G Q y).card) ≤ 18 := by
    rw [selectedCoverEdges_double_count]
    have hs := sum_le_sum (s := Q) (fun e he => subcubic_eighteen_low_cover_card_le_one G hΔ Q hQ hd hq e he)
    simpa only [sum_const, smul_eq_mul, mul_one, hq, L] using hs
  have hlS : L ⊆ selectedSupport G Q := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, by have := (mem_filter.mp hy).2; omega⟩
  have hlow (y : V) (hy : y ∈ L) : 6 ≤ (selectedCoverEdges G Q y).card := by
    have hs := subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) (hlS hy)
    have hsum := sum_le_sum (s := G.neighborFinset y) (fun z hz =>
      subcubic_eighteen_support_degree_ge_two G hΔ Q hQ hd hq (hs.2 hz))
    have hc := subcubic_large_selectedCoverEdges_count G hΔ Q hQ hd (by omega) y
    have hdy := (mem_filter.mp hy).2
    simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, hs.1] at hsum
    omega
  have hL3 : L.card ≤ 3 := by
    have hs := sum_le_sum hlow
    simp only [sum_const, smul_eq_mul] at hs
    omega
  have hlow8 (y : V) (hy : y ∈ L) : 8 ≤ (selectedCoverEdges G Q y).card := by
    have hs := subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) (hlS hy)
    have hc := subcubic_large_selectedCoverEdges_count G hΔ Q hQ hd (by omega) y
    have hdy := (mem_filter.mp hy).2
    have hsub : (G.neighborFinset y).filter (fun z => (edgeIncidences G Q z).card = 2) ⊆ L.erase y := by
      intro z hz
      obtain ⟨hzN, hdz⟩ := mem_filter.mp hz
      exact mem_erase.mpr ⟨((G.mem_neighborFinset y z).mp hzN).ne.symm,
        mem_filter.mpr ⟨mem_univ _, hdz⟩⟩
    have hcard := card_le_card hsub
    have he := card_erase_add_one hy
    have hsum : ∑ z ∈ G.neighborFinset y, ((edgeIncidences G Q z).card +
        if (edgeIncidences G Q z).card = 2 then 1 else 0) = 12 := by
      calc
        _ = ∑ _z ∈ G.neighborFinset y, 3 := by
          apply sum_congr rfl
          intro z hz
          have hl := subcubic_eighteen_support_degree_ge_two G hΔ Q hQ hd hq (hs.2 hz)
          have hu := hd z
          split_ifs <;> omega
        _ = 12 := by simp [hs.1]
    simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one] at hsum
    omega
  have hL2 : L.card ≤ 2 := by
    have hs := sum_le_sum hlow8
    simp only [sum_const, smul_eq_mul] at hs
    omega
  have hsum : (∑ y ∈ selectedSupport G Q, (edgeIncidences G Q y).card) + L.card =
      3 * (selectedSupport G Q).card := by
    have heq : (selectedSupport G Q).filter (fun y => (edgeIncidences G Q y).card = 2) = L := by
      ext y
      exact ⟨fun h => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩,
        fun h => mem_filter.mpr ⟨hlS h, (mem_filter.mp h).2⟩⟩
    calc
      _ = ∑ y ∈ selectedSupport G Q, ((edgeIncidences G Q y).card +
          if (edgeIncidences G Q y).card = 2 then 1 else 0) := by
        simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one, heq]
      _ = ∑ _y ∈ selectedSupport G Q, 3 := by
        apply sum_congr rfl
        intro y hy
        have hl := subcubic_eighteen_support_degree_ge_two G hΔ Q hQ hd hq hy
        have hu := hd y
        split_ifs <;> omega
      _ = _ := by simp [Nat.mul_comm]
  have hinc : (∑ y ∈ selectedSupport G Q, (edgeIncidences G Q y).card) = 36 := by
    have hin : edgesInside G Q (selectedSupport G Q) = Q := by
      apply filter_eq_self.mpr
      intro e he y hye
      exact mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hye⟩⟩⟩
    have hm : edgesMeeting G Q (selectedSupport G Q) = Q := by
      apply filter_eq_self.mpr
      intro e he
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      have hu : u ∈ e.val := hev ▸ Sym2.mem_mk_left u v
      exact ⟨u, mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hu⟩⟩⟩, hu⟩
    have hc := incidence_sum_eq_meeting_add_inside G Q (selectedSupport G Q)
    simpa only [hin, hm, hq] using hc
  have hempty : L.card = 0 := by omega
  have hn : (edgeIncidences G Q x).card ≠ 2 := by
    intro h
    have hp := card_pos.mpr (show L.Nonempty from ⟨x, mem_filter.mpr ⟨mem_univ _, h⟩⟩)
    omega
  have hl := subcubic_eighteen_support_degree_ge_two G hΔ Q hQ hd hq hx
  have hu := hd x
  omega

end Se20Part.Legacy
