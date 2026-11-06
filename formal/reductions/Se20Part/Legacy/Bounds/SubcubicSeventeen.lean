module

public import Se20Part.Legacy.Bounds.SubcubicBoundary

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem selectedSupport_incidence_sum (Q : Finset G.edgeSet) :
    (∑ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card) = 2 * Q.card := by
  have hin : edgesInside G Q (selectedSupport G Q) = Q := by
    apply filter_eq_self.mpr
    intro e he x hxe
    exact mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hxe⟩⟩⟩
  have hm : edgesMeeting G Q (selectedSupport G Q) = Q := by
    apply filter_eq_self.mpr
    intro e he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hu : u ∈ e.val := hev ▸ Sym2.mem_mk_left u v
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hu⟩⟩⟩, hu⟩
  have hc := incidence_sum_eq_meeting_add_inside G Q (selectedSupport G Q)
  rw [hin, hm] at hc
  omega

theorem subcubic_eighteen_support_card_twelve
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18) :
    (selectedSupport G Q).card = 12 := by
  have heq : (∑ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card) =
      ∑ _x ∈ selectedSupport G Q, 3 := by
    apply sum_congr rfl
    intro x hx
    exact subcubic_eighteen_support_degree_three G hΔ Q hQ hd hq hx
  have hc := selectedSupport_incidence_sum G Q
  simp only [sum_const, smul_eq_mul] at heq
  omega

/-- At a point outside the root and its neighbours, the selected root edges
are exactly the selected neighbours lying in the root neighbourhood. -/
theorem rootEdges_labels_at_external_point
    (Q : Finset G.edgeSet) {r x : V} (hxr : x ≠ r) (hxN : x ∉ G.neighborFinset r) :
    rootLabels G (rootEdges G Q r) x = rootLabels G Q x ∩ G.neighborFinset r := by
  ext a
  constructor
  · intro ha
    obtain ⟨haN, e, her, he⟩ := mem_filter.mp ha
    obtain ⟨hem, _⟩ := mem_filter.mp her
    obtain ⟨heQ, b, hbN, hbe⟩ := mem_filter.mp hem
    have hba : b = a := by
      rw [he, Sym2.mem_iff] at hbe
      exact hbe.elim (fun h => (hxN (h ▸ hbN)).elim) id
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨haN, e, heQ, he⟩, hba ▸ hbN⟩
  · intro ha
    obtain ⟨hal, haN⟩ := mem_inter.mp ha
    obtain ⟨hxa, e, heQ, he⟩ := mem_filter.mp hal
    have har : a ≠ r := ((G.mem_neighborFinset r a).mp haN).ne.symm
    have hr : r ∉ e.val := by simp only [he, Sym2.mem_iff]; tauto
    exact mem_filter.mpr ⟨hxa, e, mem_filter.mpr ⟨mem_filter.mpr
      ⟨heQ, a, haN, he.symm ▸ Sym2.mem_mk_right x a⟩, hr⟩, he⟩

/-- A one-unit difference between two natural counts gives this useful
bilinear lower bound, including zero counts. -/
theorem adjacent_counts_le_one_add_product (a b : ℕ)
    (hab : a ≤ b + 1) (hba : b ≤ a + 1) : a + b ≤ 1 + a * b := by
  rcases a with _ | a
  · simp only [zero_add, zero_mul, add_zero] at *; omega
  rcases b with _ | b
  · simp only [add_zero, mul_zero] at *; omega
  nlinarith [Nat.zero_le (a * b)]

theorem subcubic_eighteen_cover_inside_le_one
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    (edgesInside G Q (endpointNeighbourCover G u v)).card ≤ 1 := by
  have hs : Q.erase e ⊆ edgesMeeting G Q (endpointNeighbourCover G u v) := by
    intro f hf
    exact mem_filter.mpr ⟨(mem_erase.mp hf).2,
      strongConflict_meets_cover G he (hQ heQ (mem_erase.mp hf).2 (mem_erase.mp hf).1.symm)⟩
  have hc := card_le_card hs
  have hec := card_erase_add_one heQ
  have hi := incidence_sum_eq_meeting_add_inside G Q (endpointNeighbourCover G u v)
  have hsum := sum_le_sum (s := endpointNeighbourCover G u v) (fun x _ => hd x)
  have hcard := (subcubic_large_cover_card_and_degree G hΔ Q hQ hd (by omega) e heQ he).1
  simp only [sum_const, smul_eq_mul, hcard] at hsum
  omega

/-- Each root label uses at most three selected root incidences at its
external neighbours: two at the label itself and one opposite selected edge. -/
theorem subcubic_eighteen_label_tip_sum_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) (hq : Q.card = 18)
    {r a : V} (ha : a ∈ rootLabels G Q r) (B : Finset V)
    (hB : ∀ x ∈ B, x ≠ r ∧ x ∉ G.neighborFinset r) :
    (∑ x ∈ B.filter (G.Adj a), (edgeIncidences G (rootEdges G Q r) x).card) ≤ 3 := by
  obtain ⟨haN, e, heQ, he⟩ := mem_filter.mp ha
  let D := B.filter (G.Adj a)
  have hempty : edgesInside G (rootEdges G Q r) D = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hfr, hins⟩ := mem_filter.mp hf
    obtain ⟨_, b, hbN, hbf⟩ := mem_filter.mp (mem_filter.mp hfr).1
    exact (hB b (mem_filter.mp (hins b hbf)).1).2 hbN
  have hsub : edgesMeeting G (rootEdges G Q r) D ⊆
      (edgeIncidences G Q a).erase e ∪ edgesInside G Q (endpointNeighbourCover G r a) := by
    intro f hf
    obtain ⟨hfr, x, hxD, hxf⟩ := mem_filter.mp hf
    obtain ⟨hxB, hax⟩ := mem_filter.mp hxD
    obtain ⟨hfM, hr⟩ := mem_filter.mp hfr
    obtain ⟨hfQ, b, hbN, hbf⟩ := mem_filter.mp hfM
    have hxb : x ≠ b := fun h => (hB x hxB).2 (h.symm ▸ hbN)
    have hfval : f.val = s(x, b) := (Sym2.mem_and_mem_iff hxb).mp ⟨hxf, hbf⟩
    by_cases hba : b = a
    · apply mem_union_left
      exact mem_erase.mpr ⟨fun h => hr (h.symm ▸ he.symm ▸ Sym2.mem_mk_left r a),
        mem_filter.mpr ⟨hfQ, hba ▸ hbf⟩⟩
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hfQ, ?_⟩
      rw [hfval, Sym2.forall_mem_pair]
      exact ⟨mem_union_right _ (mem_erase.mpr ⟨(hB x hxB).1, (G.mem_neighborFinset a x).mpr hax⟩),
        mem_union_left _ (mem_erase.mpr ⟨hba, hbN⟩)⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hinside := subcubic_eighteen_cover_inside_le_one G hΔ Q hQ hd hq e heQ he
  have hec := card_erase_add_one (show e ∈ edgeIncidences G Q a from
    mem_filter.mpr ⟨heQ, he.symm ▸ Sym2.mem_mk_right r a⟩)
  have hda := hd a
  have hi := incidence_sum_eq_meeting_add_inside G (rootEdges G Q r) D
  rw [hempty, card_empty, add_zero] at hi
  change (∑ x ∈ D, (edgeIncidences G (rootEdges G Q r) x).card) ≤ 3
  omega

/-- A hypothetical eighteen-edge subcubic clique has twelve support
vertices. Counting the two kinds of incidences at one selected three-star
would require at least nine external vertices, while only seven remain. -/
theorem clique_card_le_seventeen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hd : ∀ x, (edgeIncidences G Q x).card ≤ 3) : Q.card ≤ 17 := by
  by_contra hn
  have h18 := clique_card_le_eighteen_of_support_degree_le_three G hΔ Q hQ hd
  have hq : Q.card = 18 := by omega
  have hS := subcubic_eighteen_support_card_twelve G hΔ Q hQ hd hq
  obtain ⟨r, hrS⟩ := card_pos.mp (show 0 < (selectedSupport G Q).card by omega)
  have hreg : ∀ {x}, x ∈ selectedSupport G Q →
      G.degree x = 4 ∧ G.neighborFinset x ⊆ selectedSupport G Q :=
    fun {_} hx => subcubic_large_support_closed_regular G hΔ Q hQ hd (by omega) hx
  have hcubic : ∀ {x}, x ∈ selectedSupport G Q → (edgeIncidences G Q x).card = 3 :=
    fun {_} hx => subcubic_eighteen_support_degree_three G hΔ Q hQ hd hq hx
  let A := G.neighborFinset r
  let R := rootLabels G Q r
  let B := selectedSupport G Q \ insert r A
  let t := fun x => (edgeIncidences G (rootEdges G Q r) x).card
  let s := fun x => (R.filter (G.Adj x)).card
  have hR : R.card = 3 := by dsimp [R]; rw [rootLabels_card]; exact hcubic hrS
  have hA : A.card = 4 := (hreg hrS).1
  have hRA : R ⊆ A := rootLabels_subset_neighbors G Q r
  have hAS : A ⊆ selectedSupport G Q := (hreg hrS).2
  have hN : G.IsIndepSet (G.neighborSet r) :=
    subcubic_large_root_neighborhood_independent G hΔ Q hQ hd (by omega) r
      (by change 3 ≤ R.card; omega)
  have hrA : r ∉ A := by simp [A]
  have hBcard : B.card = 7 := by
    have hs : insert r A ⊆ selectedSupport G Q := insert_subset hrS hAS
    have he := card_sdiff_add_card_eq_card hs
    rw [card_insert_of_notMem hrA, hA, hS] at he
    change B.card + _ = _ at he
    omega
  have hBx : ∀ x ∈ B, x ≠ r ∧ x ∉ G.neighborFinset r := by
    intro x hx
    have hn := (mem_sdiff.mp hx).2
    exact ⟨fun h => hn (h.symm ▸ mem_insert_self _ _), fun h => hn (mem_insert_of_mem h)⟩
  have hBsup : B ⊆ selectedSupport G Q := sdiff_subset
  have htip : rootTips G Q r ⊆ B := by
    intro x hx
    obtain ⟨_, hxr, a, haN, e, heQ, he⟩ := mem_filter.mp hx
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _, card_pos.mpr
      ⟨e, mem_filter.mpr ⟨heQ, he.symm ▸ Sym2.mem_mk_right a x⟩⟩⟩, ?_⟩
    intro h
    rcases mem_insert.mp h with h | h
    · exact hxr h
    · exact root_edge_tip_not_neighbor G hN ((G.mem_neighborFinset r a).mp haN) e he
        ((G.mem_neighborFinset r x).mp h)
  have hroot : (rootEdges G Q r).card = 9 := by
    have hi : edgesInside G Q A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨_, hp⟩ := mem_filter.mp he
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.property)
      exact hN ((G.mem_neighborFinset r u).mp (hp u (hev ▸ Sym2.mem_mk_left u v)))
        ((G.mem_neighborFinset r v).mp (hp v (hev ▸ Sym2.mem_mk_right u v))) huv.ne huv
    have hsum : (∑ a ∈ A, (edgeIncidences G Q a).card) = 12 := by
      calc
        _ = ∑ _a ∈ A, 3 := sum_congr rfl (fun a ha => hcubic (hAS ha))
        _ = 12 := by simp [hA]
    have hc := incidence_sum_eq_meeting_add_inside G Q A
    rw [hi, card_empty, add_zero, hsum] at hc
    have hf : (edgesMeeting G Q A).filter (fun e => r ∈ e.val) = edgeIncidences G Q r := by
      ext e
      constructor
      · intro h; exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩
      · intro h
        obtain ⟨heQ, hre⟩ := mem_filter.mp h
        obtain ⟨a, hea⟩ := Sym2.mem_iff_exists.mp hre
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨heQ, a,
          (G.mem_neighborFinset r a).mpr (G.mem_edgeSet.mp (hea ▸ e.property)),
          hea.symm ▸ Sym2.mem_mk_right r a⟩, hre⟩
    have hp := card_filter_add_card_filter_not (s := edgesMeeting G Q A) (p := fun e => r ∈ e.val)
    rw [hf, hcubic hrS, ← hc] at hp
    change 3 + (rootEdges G Q r).card = 12 at hp
    omega
  have htSum : (∑ x ∈ B, t x) = 9 := by
    have hi : edgesInside G (rootEdges G Q r) B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨her, hp⟩ := mem_filter.mp he
      obtain ⟨_, a, haN, hae⟩ := mem_filter.mp (mem_filter.mp her).1
      exact (hBx a (hp a hae)).2 haN
    have hm : edgesMeeting G (rootEdges G Q r) B = rootEdges G Q r := by
      apply filter_eq_self.mpr
      intro e he
      obtain ⟨hem, hr⟩ := mem_filter.mp he
      obtain ⟨heQ, a, haN, hae⟩ := mem_filter.mp hem
      obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp hae
      have hxr : x ≠ r := fun h => hr (hex.symm ▸ h ▸ Sym2.mem_mk_right a x)
      exact ⟨x, htip (mem_filter.mpr ⟨mem_univ _, hxr, a, haN, e, heQ, hex⟩),
        hex.symm ▸ Sym2.mem_mk_right a x⟩
    have hc := incidence_sum_eq_meeting_add_inside G (rootEdges G Q r) B
    simpa only [hi, hm, card_empty, add_zero, hroot] using hc
  have hneighbors (a : V) (ha : a ∈ R) : B.filter (G.Adj a) = (G.neighborFinset a).erase r := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxB, hax⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨(hBx x hxB).1, (G.mem_neighborFinset a x).mpr hax⟩
    · intro hx
      obtain ⟨hxr, hxN⟩ := mem_erase.mp hx
      have hax := (G.mem_neighborFinset a x).mp hxN
      have haA := hRA ha
      have hxS := (hreg (hAS haA)).2 hxN
      apply mem_filter.mpr
      refine ⟨mem_sdiff.mpr ⟨hxS, ?_⟩, hax⟩
      intro h
      rcases mem_insert.mp h with h | h
      · exact hxr h
      · exact hN ((G.mem_neighborFinset r a).mp haA) ((G.mem_neighborFinset r x).mp h) hax.ne hax
  have hsSum : (∑ x ∈ B, s x) = 9 := by
    have heq : (∑ x ∈ B, s x) = ∑ a ∈ R, (B.filter (G.Adj a)).card := by
      simp only [s, card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro x _
      simp only [G.adj_comm]
    rw [heq]
    calc
      _ = ∑ _a ∈ R, 3 := by
        apply sum_congr rfl
        intro a ha
        rw [hneighbors a ha]
        have hc := card_erase_add_one ((G.mem_neighborFinset a r).mpr
          ((G.mem_neighborFinset r a).mp (hRA ha)).symm)
        have hda := (hreg (hAS (hRA ha))).1
        simp only [SimpleGraph.card_neighborFinset_eq_degree, hda] at hc
        omega
      _ = 9 := by simp [hR]
  have hpSum : (∑ x ∈ B, s x * t x) ≤ 9 := by
    have heq : (∑ x ∈ B, s x * t x) = ∑ a ∈ R, ∑ x ∈ B.filter (G.Adj a), t x := by
      simp only [s, card_eq_sum_ones, sum_filter, sum_mul, ite_mul, one_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro x _
      simp only [G.adj_comm]
    rw [heq]
    have hs := sum_le_sum (s := R) (fun a ha =>
      subcubic_eighteen_label_tip_sum_le_three G hΔ Q hQ hd hq ha B hBx)
    simpa only [sum_const, smul_eq_mul, hR] using hs
  have hpoint (x : V) (hx : x ∈ B) : s x + t x ≤ 1 + s x * t x := by
    let N := G.neighborFinset x
    let U := rootLabels G Q x
    have hUN : U ⊆ N := rootLabels_subset_neighbors G Q x
    have hNU : (N \ U).card = 1 := by
      have hc := card_sdiff_add_card_eq_card hUN
      have huc : U.card = 3 := by dsimp [U]; rw [rootLabels_card]; exact hcubic (hBsup hx)
      have hnc : N.card = 4 := (hreg (hBsup hx)).1
      omega
    have hAR : (A \ R).card = 1 := by
      have hc := card_sdiff_add_card_eq_card hRA
      omega
    have hs : s x = (N ∩ R).card := by
      change (R.filter (G.Adj x)).card = (N ∩ R).card
      apply congrArg Finset.card
      ext a
      simp only [mem_filter, N, mem_inter, SimpleGraph.mem_neighborFinset, and_comm]
    have ht : t x = (U ∩ A).card := by
      dsimp [t, U, A]
      rw [← rootLabels_card, rootEdges_labels_at_external_point G Q (hBx x hx).1 (hBx x hx).2]
    have hsSub : N ∩ R ⊆ (U ∩ A) ∪ (N \ U) := by
      intro a ha
      obtain ⟨haN, haR⟩ := mem_inter.mp ha
      by_cases haU : a ∈ U
      · exact mem_union_left _ (mem_inter.mpr ⟨haU, hRA haR⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨haN, haU⟩)
    have htSub : U ∩ A ⊆ (N ∩ R) ∪ (A \ R) := by
      intro a ha
      obtain ⟨haU, haA⟩ := mem_inter.mp ha
      by_cases haR : a ∈ R
      · exact mem_union_left _ (mem_inter.mpr ⟨hUN haU, haR⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨haA, haR⟩)
    have hsc := (card_le_card hsSub).trans (card_union_le _ _)
    have htc := (card_le_card htSub).trans (card_union_le _ _)
    apply adjacent_counts_le_one_add_product
    · omega
    · omega
  have htotal := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, hBcard, hsSum, htSum] at htotal
  omega

end Se20Part.Legacy
