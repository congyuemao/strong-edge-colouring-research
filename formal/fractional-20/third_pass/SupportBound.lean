import second_pass.PropositionDReduction

namespace Se20Fractional.ThirdPass
open Finset DReduction
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def selectedAt (Q : Finset G.edgeSet) (v : V) :=
  Q.filter (fun e => v ∈ e.val)

noncomputable def labels (Q : Finset G.edgeSet) (r : V) :=
  (G.neighborFinset r).filter (fun a => ∃ h : G.Adj r a,
    (⟨s(r,a),h⟩ : G.edgeSet) ∈ Q)

theorem mem_labels (Q : Finset G.edgeSet) (r a : V) :
    a ∈ labels Q r ↔ ∃ h : G.Adj r a, (⟨s(r,a),h⟩ : G.edgeSet) ∈ Q := by
  simp only [labels, mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.choose,h⟩⟩

theorem labels_card (Q : Finset G.edgeSet) (r : V) :
    (labels Q r).card = (selectedAt Q r).card := by
  apply Finset.card_bij (fun a ha => (⟨s(r,a), ((mem_labels Q r a).mp ha).choose⟩ : G.edgeSet))
  · intro a ha
    exact mem_filter.mpr ⟨((mem_labels Q r a).mp ha).choose_spec, by simp⟩
  · intro a ha b hb hab
    have h := Sym2.eq_iff.mp (congrArg Subtype.val hab)
    rcases h with h | h <;> grind
  · intro e he
    obtain ⟨heQ,her⟩ := mem_filter.mp he
    rcases e with ⟨e,heG⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp her with h | h
      · subst a
        exact ⟨b,(mem_labels Q r b).mpr ⟨heG,heQ⟩,rfl⟩
      · subst b
        have heq : (⟨s(r,a),heG.symm⟩ : G.edgeSet) = ⟨s(a,r),heG⟩ :=
          Subtype.ext (Sym2.eq_swap)
        exact ⟨a,(mem_labels Q r a).mpr ⟨heG.symm,heq.symm ▸ heQ⟩,heq⟩

theorem selected_neighbor (Q : Finset G.edgeSet) {x : V} (hx : x ∈ endpoints Q) :
    ∃ y, ∃ h : G.Adj x y, (⟨s(x,y),h⟩ : G.edgeSet) ∈ Q := by
  obtain ⟨⟨e,heG⟩,heQ,hxe⟩ := (mem_endpoints Q x).mp hx
  induction e using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.mp hxe with h | h
    · subst a; exact ⟨b,heG,heQ⟩
    · subst b
      have heq : (⟨s(x,a),heG.symm⟩ : G.edgeSet) = ⟨s(a,x),heG⟩ :=
        Subtype.ext Sym2.eq_swap
      exact ⟨a,heG.symm,heq.symm ▸ heQ⟩

theorem clique_card_le_thirteen_of_selected_degree_le_two
    (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (h₂ : ∀ v, (selectedAt Q v).card ≤ 2) :
    Q.card ≤ 13 := by
  by_cases hne : Q.Nonempty
  · obtain ⟨⟨e,heG⟩,heQ⟩ := hne
    induction e using Sym2.ind with
    | _ a b =>
      let e : G.edgeSet := ⟨s(a,b),heG⟩
      let R := endpointRegion G a b
      have hs : Q.erase e ⊆ R.biUnion (selectedAt Q) := by
        intro f hf
        obtain ⟨hne,hfQ⟩ := mem_erase.mp hf
        obtain ⟨x,hxf,hxR⟩ := (l2_adj_region G a b heG f).mp (hQ e heQ f hfQ hne.symm)
        exact mem_biUnion.mpr ⟨x,hxR,mem_filter.mpr ⟨hfQ,hxf⟩⟩
      have hc := (card_le_card hs).trans Finset.card_biUnion_le
      have hsum := Finset.sum_le_sum (s := R) (fun x _ => h₂ x)
      have hr := endpointRegion_card G a b heG
      have ha := hΔ a
      have hb := hΔ b
      have he : (Q.erase e).card + 1 = Q.card := card_erase_add_one heQ
      simp only [sum_const, smul_eq_mul] at hsum
      change _ ≤ R.card * 2 at hsum
      change R.card + 2 + _ = _ at hr
      omega
  · have : Q = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [this]

theorem exists_three_labels (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hsize : 14 ≤ Q.card) :
    ∃ r, 3 ≤ (labels Q r).card := by
  by_contra! hn
  have h₂ : ∀ v, (selectedAt Q v).card ≤ 2 := by
    intro v
    have := hn v
    rw [labels_card] at this
    omega
  have := clique_card_le_thirteen_of_selected_degree_le_two hΔ Q hQ h₂
  omega

noncomputable def tip (G : SimpleGraph V) (r x : V) :=
  G.neighborFinset x ∩ G.neighborFinset r

theorem mem_tip (r x a : V) : a ∈ tip G r x ↔ G.Adj x a ∧ G.Adj r a := by
  simp [tip]

theorem outer_cover (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    {r x y : V} (hxr : x ≠ r) (hyr : y ≠ r) (hrx : ¬ G.Adj r x)
    (hry : ¬ G.Adj r y) (hxy : G.Adj x y)
    (hxyQ : (⟨s(x,y),hxy⟩ : G.edgeSet) ∈ Q) :
    labels Q r ⊆ tip G r x ∪ tip G r y := by
  intro a ha
  obtain ⟨hra,hraQ⟩ := (mem_labels Q r a).mp ha
  have hne : (⟨s(r,a),hra⟩ : G.edgeSet) ≠ ⟨s(x,y),hxy⟩ := by
    intro h
    have := Sym2.eq_iff.mp (congrArg Subtype.val h)
    grind
  obtain ⟨_,u,hu,v,hv,huv⟩ := hQ _ hraQ _ hxyQ hne
  simp only [Sym2.mem_iff] at hu hv
  simp only [mem_union, mem_tip]
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  all_goals grind [SimpleGraph.Adj.symm]

theorem tip_sum_le_twelve (hΔ : ∀ v, G.degree v ≤ 4) (r : V)
    (U : Finset V) (hr : r ∉ U) : ∑ x ∈ U, (tip G r x).card ≤ 12 := by
  have heq : ∑ x ∈ U, (tip G r x).card =
      ∑ a ∈ G.neighborFinset r, (U.filter (fun x => G.Adj a x)).card := by
    have ht (x : V) : (tip G r x).card =
        ∑ a ∈ G.neighborFinset r, if G.Adj a x then 1 else 0 := by
      rw [← card_filter]
      congr 1
      ext a
      simp [tip, G.adj_comm, and_comm]
    simp_rw [ht, card_filter]
    exact sum_comm
  rw [heq]
  have hb : ∀ a ∈ G.neighborFinset r, (U.filter (fun x => G.Adj a x)).card ≤ 3 := by
    intro a ha
    have hs : U.filter (fun x => G.Adj a x) ⊆ (G.neighborFinset a).erase r := by
      intro x hx
      obtain ⟨hxU,hax⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨fun h => hr (h ▸ hxU), (G.mem_neighborFinset a x).mpr hax⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr
      ((G.mem_neighborFinset r a).mp ha).symm)
    have hd := hΔ a
    rw [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  have hs := sum_le_sum hb
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  have := hΔ r
  omega

theorem residual_unique (hΔ : ∀ v, G.degree v ≤ 4) {r y x z : V}
    (ht : 3 ≤ (tip G r y).card) (hyx : G.Adj y x) (hyz : G.Adj y z)
    (hrx : ¬ G.Adj r x) (hrz : ¬ G.Adj r z) : x = z := by
  let B := G.neighborFinset y \ G.neighborFinset r
  have hc : B.card + (tip G r y).card = G.degree y := by
    simpa only [B, tip, SimpleGraph.card_neighborFinset_eq_degree] using
      card_sdiff_add_card_inter (G.neighborFinset y) (G.neighborFinset r)
  have hd := hΔ y
  have hb : B.card ≤ 1 := by omega
  have hx : x ∈ B := mem_sdiff.mpr ⟨by simpa using hyx, by simpa using hrx⟩
  have hz : z ∈ B := mem_sdiff.mpr ⟨by simpa using hyz, by simpa using hrz⟩
  exact (card_le_one.mp hb) x hx z hz

/-- An endpoint with empty type forces a distinct triple tip; a triple tip
has room for at most one such endpoint. -/
theorem empty_tip_partner (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    {r : V} (hs : 3 ≤ (labels Q r).card) {x : V}
    (hx : x ∈ endpoints Q) (hxr : x ≠ r) (hrx : ¬ G.Adj r x)
    (htx : tip G r x = ∅) :
    ∃ y, y ∈ endpoints Q ∧ y ≠ r ∧ ¬ G.Adj r y ∧
      3 ≤ (tip G r y).card ∧ G.Adj x y := by
  obtain ⟨y,hxy,hxyQ⟩ := selected_neighbor Q hx
  have hyr : y ≠ r := by intro h; subst y; exact hrx hxy.symm
  have hry : ¬ G.Adj r y := by
    intro h
    have hyT : y ∈ tip G r x := (mem_tip r x y).mpr ⟨hxy,h⟩
    rw [htx] at hyT
    exact notMem_empty _ hyT
  have hcov := outer_cover Q hQ hxr hyr hrx hry hxy hxyQ
  rw [htx, empty_union] at hcov
  exact ⟨y, (mem_endpoints Q y).mpr ⟨_,hxyQ,by simp⟩, hyr, hry,
    hs.trans (card_le_card hcov), hxy⟩

theorem outer_support_bound (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    {r : V} (hs : 3 ≤ (labels Q r).card) :
    (endpoints Q \ insert r (G.neighborFinset r)).card ≤ 12 := by
  let U := endpoints Q \ insert r (G.neighborFinset r)
  let Z := U.filter (fun x => tip G r x = ∅)
  let T := U.filter (fun x => 3 ≤ (tip G r x).card)
  have hU (x : V) : x ∈ U ↔ x ∈ endpoints Q ∧ x ≠ r ∧ ¬ G.Adj r x := by
    simp [U, not_or]
  have hw (x : V) (hx : x ∈ Z) : ∃ y, y ∈ T ∧ G.Adj x y := by
    obtain ⟨hxU,hxT⟩ := mem_filter.mp hx
    obtain ⟨hxQ,hxr,hrx⟩ := (hU x).mp hxU
    obtain ⟨y,hyQ,hyr,hry,hyT,hxy⟩ := empty_tip_partner Q hQ hs hxQ hxr hrx hxT
    exact ⟨y,mem_filter.mpr ⟨(hU y).mpr ⟨hyQ,hyr,hry⟩,hyT⟩,hxy⟩
  have hZT : Z.card ≤ T.card := by
    let f (x : V) := if hx : x ∈ Z then (hw x hx).choose else r
    have hf (x : V) (hx : x ∈ Z) : f x ∈ T ∧ G.Adj x (f x) := by
      simpa only [f, dite_eq_left hx] using (hw x hx).choose_spec
    apply card_le_card_of_injOn f
    · exact fun x hx => (hf x hx).1
    · intro x hx z hz heq
      have hfx := hf x hx
      have hfz := hf z hz
      rw [← heq] at hfz
      exact residual_unique hΔ (mem_filter.mp hfx.1).2 hfx.2.symm hfz.2.symm
        ((hU x).mp (mem_filter.mp hx).1).2.2
        ((hU z).mp (mem_filter.mp hz).1).2.2
  have hsum := sum_le_sum (s := U) (f := fun x => 1 + 2 * (if x ∈ T then 1 else 0))
    (g := fun x => (tip G r x).card + (if x ∈ Z then 1 else 0)) (by
      intro x hx
      by_cases hz : x ∈ Z
      · have ht0 := (mem_filter.mp hz).2
        have hnt : x ∉ T := by simp [T, ht0]
        simp [hz,hnt,ht0]
      · have hp : 1 ≤ (tip G r x).card := by
          have hn : tip G r x ≠ ∅ := fun h => hz (mem_filter.mpr ⟨hx,h⟩)
          exact card_pos.mpr (nonempty_iff_ne_empty.mpr hn)
        by_cases ht : x ∈ T
        · have h3 := (mem_filter.mp ht).2
          simp only [ht, hz, ite_true, ite_false, mul_one, add_zero]
          exact h3
        · simp only [ht, hz, ite_false, mul_zero, add_zero]
          exact hp)
  have hTf : U.filter (fun x => x ∈ T) = T := by ext x; simp [T]
  have hZf : U.filter (fun x => x ∈ Z) = Z := by ext x; simp [Z]
  simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one,
    ← card_filter, hTf, hZf] at hsum
  have hr : r ∉ U := by simp [U]
  have h12 := tip_sum_le_twelve hΔ r U hr
  change U.card ≤ 12
  omega

/-- A support bound independent of the local rim hypothesis. -/
theorem endpoint_bound_17 (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hsize : 14 ≤ Q.card) : (endpoints Q).card ≤ 17 := by
  obtain ⟨r,hs⟩ := exists_three_labels hΔ Q hQ hsize
  have ho := outer_support_bound hΔ Q hQ hs
  have hc := card_sdiff_add_card_inter (endpoints Q) (insert r (G.neighborFinset r))
  have hi := card_le_card (inter_subset_right :
    endpoints Q ∩ insert r (G.neighborFinset r) ⊆ insert r (G.neighborFinset r))
  have hn := card_insert_le r (G.neighborFinset r)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hn
  have hd := hΔ r
  omega

#print axioms endpoint_bound_17

end Se20Fractional.ThirdPass
