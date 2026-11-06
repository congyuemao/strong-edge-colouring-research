import third_pass.SupportBound

namespace Se20Fractional.ThirdPass
open Finset DReduction
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def outerSupport (Q : Finset G.edgeSet) (r : V) :=
  endpoints Q \ insert r (G.neighborFinset r)

theorem mem_outerSupport (Q : Finset G.edgeSet) (r x : V) :
    x ∈ outerSupport Q r ↔ x ∈ endpoints Q ∧ x ≠ r ∧ ¬ G.Adj r x := by
  simp [outerSupport, not_or]

noncomputable def outerSelected (Q : Finset G.edgeSet) (r : V) :=
  Q.filter (fun e => ∀ x ∈ e.val, x ∈ outerSupport Q r)

noncomputable def crossSelected (Q : Finset G.edgeSet) (r : V) :=
  Q.filter (fun e => (∃ a ∈ e.val, G.Adj r a) ∧
    ∃ x ∈ e.val, x ∈ outerSupport Q r)

theorem selected_cover_bound (Q : Finset G.edgeSet) (S : Finset V)
    (h : ∀ e ∈ Q, ∃ x ∈ e.val, x ∈ S) :
    Q.card ≤ ∑ x ∈ S, (selectedAt Q x).card := by
  have hs : Q ⊆ S.biUnion (selectedAt Q) := by
    intro e he
    obtain ⟨x,hxe,hxS⟩ := h e he
    exact mem_biUnion.mpr ⟨x,hxS,mem_filter.mpr ⟨he,hxe⟩⟩
  exact (card_le_card hs).trans card_biUnion_le

theorem selected_incidence_sum (Q : Finset G.edgeSet) (S : Finset V) :
    (∑ x ∈ S, (selectedAt Q x).card) =
      (Q.filter (fun e => ∃ x ∈ e.val, x ∈ S)).card +
      (Q.filter (fun e => ∀ x ∈ e.val, x ∈ S)).card := by
  simp only [selectedAt, card_filter]
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  rcases e with ⟨e,heG⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := heG.ne
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq]
    have hi (x : V) : (if x = a ∨ x = b then 1 else 0 : ℕ) =
        (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
      by_cases ha : x = a <;> by_cases hb : x = b <;> simp_all
    simp_rw [hi]
    rw [sum_add_distrib]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha,hb]

theorem cross_degree_le_tip (Q : Finset G.edgeSet) (r : V) {x : V}
    (hx : x ∈ outerSupport Q r) :
    (selectedAt (crossSelected Q r) x).card ≤ (tip G r x).card := by
  rw [← labels_card]
  apply card_le_card
  intro a ha
  obtain ⟨hxa,he⟩ := (mem_labels _ x a).mp ha
  obtain ⟨_,hA,_⟩ := mem_filter.mp he
  have hrx := ((mem_outerSupport Q r x).mp hx).2.2
  simp only [Sym2.mem_iff, exists_eq_or_imp, exists_eq] at hA
  exact (mem_tip r x a).mpr ⟨hxa,by grind⟩

theorem cross_incidence_sum (Q : Finset G.edgeSet) (r : V) :
    (∑ x ∈ outerSupport Q r, (selectedAt (crossSelected Q r) x).card) =
      (crossSelected Q r).card := by
  rw [selected_incidence_sum]
  have htouch : (crossSelected Q r).filter (fun e =>
      ∃ x ∈ e.val, x ∈ outerSupport Q r) = crossSelected Q r := by
    apply filter_eq_self.mpr
    intro e he
    exact (mem_filter.mp he).2.2
  have hinside : (crossSelected Q r).filter (fun e =>
      ∀ x ∈ e.val, x ∈ outerSupport Q r) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heK,hU⟩ := mem_filter.mp he
    obtain ⟨_,⟨a,ha,hra⟩,_⟩ := mem_filter.mp heK
    exact ((mem_outerSupport Q r a).mp (hU a ha)).2.2 hra
  rw [htouch,hinside,card_empty,add_zero]

theorem root_partition_bound (Q : Finset G.edgeSet) (r : V)
    (hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b) :
    Q.card ≤ (labels Q r).card + (crossSelected Q r).card +
      (outerSelected Q r).card := by
  have hs : Q ⊆ (selectedAt Q r ∪ crossSelected Q r) ∪ outerSelected Q r := by
    intro e he
    by_cases hr : r ∈ e.val
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨he,hr⟩))
    by_cases hK : e ∈ crossSelected Q r
    · exact mem_union_left _ (mem_union_right _ hK)
    apply mem_union_right
    apply mem_filter.mpr
    refine ⟨he, ?_⟩
    rcases e with ⟨e,heG⟩
    induction e using Sym2.ind with
    | _ a b =>
      have haQ : a ∈ endpoints Q := (mem_endpoints Q a).mpr ⟨_,he,by simp⟩
      have hbQ : b ∈ endpoints Q := (mem_endpoints Q b).mpr ⟨_,he,by simp⟩
      have har : a ≠ r := by intro h; exact hr (h ▸ Sym2.mem_mk_left a b)
      have hbr : b ≠ r := by intro h; exact hr (h ▸ Sym2.mem_mk_right a b)
      have hra : ¬ G.Adj r a := by
        intro hra
        have hrb : ¬ G.Adj r b := fun hrb => hA a b hra hrb heG
        exact hK (mem_filter.mpr ⟨he,⟨a,by simp,hra⟩,
          b,by simp,(mem_outerSupport Q r b).mpr ⟨hbQ,hbr,hrb⟩⟩)
      have hrb : ¬ G.Adj r b := by
        intro hrb
        exact hK (mem_filter.mpr ⟨he,⟨b,by simp,hrb⟩,
          a,by simp,(mem_outerSupport Q r a).mpr ⟨haQ,har,hra⟩⟩)
      intro x hx
      rcases Sym2.mem_iff.mp hx with h | h
      · subst x; exact (mem_outerSupport Q r a).mpr ⟨haQ,har,hra⟩
      · subst x; exact (mem_outerSupport Q r b).mpr ⟨hbQ,hbr,hrb⟩
  have hc := card_le_card hs
  have hu := card_union_le (selectedAt Q r ∪ crossSelected Q r) (outerSelected Q r)
  have hv := card_union_le (selectedAt Q r) (crossSelected Q r)
  rw [labels_card]
  omega

theorem outer_incidence_capacity (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (r x : V) :
    (selectedAt (outerSelected Q r) x).card + (tip G r x).card ≤ 4 := by
  have hs : labels (outerSelected Q r) x ⊆ G.neighborFinset x \ G.neighborFinset r := by
    intro y hy
    obtain ⟨hxy,he⟩ := (mem_labels _ x y).mp hy
    have hyU := (mem_filter.mp he).2 y (by simp)
    exact mem_sdiff.mpr ⟨by simpa using hxy,
      by simpa using ((mem_outerSupport Q r y).mp hyU).2.2⟩
  have hc := card_le_card hs
  rw [labels_card] at hc
  have hi := card_sdiff_add_card_inter (G.neighborFinset x) (G.neighborFinset r)
  change _ + (tip G r x).card = _ at hi
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hi
  have hd := hΔ x
  omega

theorem outer_meets_multiple (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    {r : V} (hs : 3 ≤ (labels Q r).card) :
    ∀ e ∈ outerSelected Q r, ∃ x ∈ e.val,
      x ∈ outerSupport Q r ∧ 2 ≤ (tip G r x).card := by
  rintro ⟨e,heG⟩ he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨heQ,hU⟩ := mem_filter.mp he
    have hx := (mem_outerSupport Q r x).mp (hU x (by simp))
    have hy := (mem_outerSupport Q r y).mp (hU y (by simp))
    have hc := card_le_card (outer_cover Q hQ hx.2.1 hy.2.1 hx.2.2 hy.2.2 heG heQ)
    have hu := card_union_le (tip G r x) (tip G r y)
    by_cases htx : 2 ≤ (tip G r x).card
    · exact ⟨x,by simp,hU x (by simp),htx⟩
    · exact ⟨y,by simp,hU y (by simp),by omega⟩

noncomputable def zeroTips (Q : Finset G.edgeSet) (r : V) :=
  (outerSupport Q r).filter (fun x => tip G r x = ∅)
noncomputable def tripleTips (Q : Finset G.edgeSet) (r : V) :=
  (outerSupport Q r).filter (fun x => 3 ≤ (tip G r x).card)
noncomputable def selectedTips (Q : Finset G.edgeSet) (r : V) :=
  (outerSupport Q r).filter (fun x => 0 < (selectedAt (crossSelected Q r) x).card)
noncomputable def excess (Q : Finset G.edgeSet) (r : V) :=
  ∑ x ∈ outerSupport Q r, ((tip G r x).card - 1)

theorem zero_le_triple (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) {r : V} (hs : 3 ≤ (labels Q r).card) :
    (zeroTips Q r).card ≤ (tripleTips Q r).card := by
  have hw (x : V) (hx : x ∈ zeroTips Q r) : ∃ y, y ∈ tripleTips Q r ∧ G.Adj x y := by
    obtain ⟨hxU,hxT⟩ := mem_filter.mp hx
    obtain ⟨hxQ,hxr,hrx⟩ := (mem_outerSupport Q r x).mp hxU
    obtain ⟨y,hyQ,hyr,hry,hyT,hxy⟩ := empty_tip_partner Q hQ hs hxQ hxr hrx hxT
    exact ⟨y,mem_filter.mpr ⟨(mem_outerSupport Q r y).mpr ⟨hyQ,hyr,hry⟩,hyT⟩,hxy⟩
  let f (x : V) := if hx : x ∈ zeroTips Q r then (hw x hx).choose else r
  have hf (x : V) (hx : x ∈ zeroTips Q r) : f x ∈ tripleTips Q r ∧ G.Adj x (f x) := by
    simpa only [f, dite_eq_left hx] using (hw x hx).choose_spec
  apply card_le_card_of_injOn f
  · exact fun x hx => (hf x hx).1
  · intro x hx z hz heq
    have hfx := hf x hx
    have hfz := hf z hz
    rw [← heq] at hfz
    exact residual_unique hΔ (mem_filter.mp hfx.1).2 hfx.2.symm hfz.2.symm
      ((mem_outerSupport Q r x).mp (mem_filter.mp hx).1).2.2
      ((mem_outerSupport Q r z).mp (mem_filter.mp hz).1).2.2

theorem type_budget (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet) (r : V) :
    (outerSupport Q r).card + excess Q r ≤ 12 + (zeroTips Q r).card := by
  have heq : (outerSupport Q r).card + excess Q r =
      (∑ x ∈ outerSupport Q r, (tip G r x).card) + (zeroTips Q r).card := by
    have hp (x : V) : 1 + ((tip G r x).card - 1) =
        (tip G r x).card + if tip G r x = ∅ then 1 else 0 := by
      by_cases ht : tip G r x = ∅
      · simp [ht]
      · have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr ht)
        simp only [ht, ite_false, add_zero]
        omega
    have h := sum_congr (s₁ := outerSupport Q r) rfl (fun x _ => hp x)
    simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one,
      ← card_filter, excess, zeroTips] using h
  have hr : r ∉ outerSupport Q r := by simp [outerSupport]
  have h := tip_sum_le_twelve hΔ r (outerSupport Q r) hr
  omega

theorem triple_budget (Q : Finset G.edgeSet) (r : V) :
    2 * (tripleTips Q r).card ≤ excess Q r := by
  have h := sum_le_sum (s := outerSupport Q r)
    (f := fun x => 2 * if 3 ≤ (tip G r x).card then 1 else 0)
    (g := fun x => (tip G r x).card - 1) (by
      intro x hx
      split_ifs with ht <;> omega)
  simpa only [tripleTips, excess, ← mul_sum, ← card_filter] using h

theorem outer_budget (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) {r : V} (hs : 3 ≤ (labels Q r).card) :
    (outerSelected Q r).card + 3 * (tripleTips Q r).card ≤ 2 * excess Q r := by
  let M := (outerSupport Q r).filter (fun x => 2 ≤ (tip G r x).card)
  have hcov := selected_cover_bound (outerSelected Q r) M (by
    intro e he
    obtain ⟨x,hxe,hxU,hxt⟩ := outer_meets_multiple Q hQ hs e he
    exact ⟨x,hxe,mem_filter.mpr ⟨hxU,hxt⟩⟩)
  have h := sum_le_sum (s := outerSupport Q r)
    (f := fun x => (if 2 ≤ (tip G r x).card then (selectedAt (outerSelected Q r) x).card else 0) +
      3 * if 3 ≤ (tip G r x).card then 1 else 0)
    (g := fun x => 2 * ((tip G r x).card - 1)) (by
      intro x hx
      have hc := outer_incidence_capacity hΔ Q r x
      split_ifs <;> omega)
  simp only [sum_add_distrib, ← sum_filter, ← mul_sum, sum_const, smul_eq_mul, mul_one] at h
  change (∑ x ∈ M, (selectedAt (outerSelected Q r) x).card) +
    3 * (tripleTips Q r).card ≤ 2 * excess Q r at h
  omega

theorem cross_budget (Q : Finset G.edgeSet) (r : V) :
    (crossSelected Q r).card ≤ (selectedTips Q r).card + excess Q r := by
  have h := sum_le_sum (s := outerSupport Q r)
    (f := fun x => (selectedAt (crossSelected Q r) x).card)
    (g := fun x => (if 0 < (selectedAt (crossSelected Q r) x).card then 1 else 0) +
      ((tip G r x).card - 1)) (by
      intro x hx
      have hb := cross_degree_le_tip Q r hx
      split_ifs <;> omega)
  simpa only [cross_incidence_sum, sum_add_distrib, ← card_filter, selectedTips, excess] using h

theorem cross_budget_no_single (Q : Finset G.edgeSet) (r : V)
    (hn : ∀ x ∈ selectedTips Q r, (tip G r x).card ≠ 1) :
    (crossSelected Q r).card ≤ 2 * excess Q r := by
  have h := sum_le_sum (s := outerSupport Q r)
    (f := fun x => (selectedAt (crossSelected Q r) x).card)
    (g := fun x => 2 * ((tip G r x).card - 1)) (by
      intro x hx
      have hb := cross_degree_le_tip Q r hx
      by_cases hp : 0 < (selectedAt (crossSelected Q r) x).card
      · have ht := hn x (mem_filter.mpr ⟨hx,hp⟩)
        omega
      · omega)
  simpa only [cross_incidence_sum, ← mul_sum, excess] using h

theorem selected_tip_edge (Q : Finset G.edgeSet) (r : V) {x : V}
    (hx : x ∈ selectedTips Q r) :
    ∃ a, G.Adj r a ∧ ∃ h : G.Adj a x, (⟨s(a,x),h⟩ : G.edgeSet) ∈ Q := by
  obtain ⟨hxU,hxp⟩ := mem_filter.mp hx
  obtain ⟨e,he⟩ := card_pos.mp hxp
  obtain ⟨heK,hxe⟩ := mem_filter.mp he
  obtain ⟨a,hxa,haK⟩ := selected_neighbor (crossSelected Q r)
    ((mem_endpoints _ x).mpr ⟨e,heK,hxe⟩)
  have haT : a ∈ tip G r x := by
    have hA := (mem_filter.mp haK).2.1
    have hrx := ((mem_outerSupport Q r x).mp hxU).2.2
    apply (mem_tip r x a).mpr
    refine ⟨hxa,?_⟩
    simp only [Sym2.mem_iff] at hA
    grind
  have heq : (⟨s(a,x),hxa.symm⟩ : G.edgeSet) = ⟨s(x,a),hxa⟩ :=
    Subtype.ext Sym2.eq_swap
  exact ⟨a,((mem_tip r x a).mp haT).2,hxa.symm,heq.symm ▸ (mem_filter.mp haK).1⟩

theorem single_tip_bound (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) {r : V}
    (hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b)
    {x : V} (hx : x ∈ selectedTips Q r) (ht : (tip G r x).card = 1) :
    (selectedTips Q r).card ≤ 6 := by
  obtain ⟨a,hra,hax,haxQ⟩ := selected_tip_edge Q r hx
  have hta : a ∈ tip G r x := (mem_tip r x a).mpr ⟨hax.symm,hra⟩
  have htEq : tip G r x = {a} := by
    obtain ⟨b,hb⟩ := card_eq_one.mp ht
    rw [hb] at hta
    have : a = b := mem_singleton.mp hta
    subst b
    exact hb
  have hsub : selectedTips Q r ⊆ (G.neighborFinset a).erase r ∪ (G.neighborFinset x).erase a := by
    intro y hy
    have hyU := (mem_filter.mp hy).1
    have hyR := (mem_outerSupport Q r y).mp hyU
    by_cases hay : G.Adj a y
    · exact mem_union_left _ (mem_erase.mpr ⟨hyR.2.1,by simpa using hay⟩)
    obtain ⟨b,hrb,hby,hbyQ⟩ := selected_tip_edge Q r hy
    have hba : b ≠ a := by intro h; subst b; exact hay hby
    have hbx : ¬ G.Adj b x := by
      intro h
      have hbT : b ∈ tip G r x := (mem_tip r x b).mpr ⟨h.symm,hrb⟩
      rw [htEq] at hbT
      exact hba (mem_singleton.mp hbT)
    have hab : ¬ G.Adj a b := hA a b hra hrb
    have hne : (⟨s(a,x),hax⟩ : G.edgeSet) ≠ ⟨s(b,y),hby⟩ := by
      intro h
      have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
      have hxr := ((mem_outerSupport Q r x).mp (mem_filter.mp hx).1).2.2
      grind
    obtain ⟨_,u,hu,v,hv,huv⟩ := hQ _ haxQ _ hbyQ hne
    have hxy : G.Adj x y := by
      simp only [Sym2.mem_iff] at hu hv
      rcases hu with h | h <;> rcases hv with h' | h'
      all_goals subst u; subst v
      all_goals grind [SimpleGraph.Adj.symm]
    have hya : y ≠ a := by intro h; subst y; exact hyR.2.2 hra
    exact mem_union_right _ (mem_erase.mpr ⟨hya,by simpa using hxy⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have ha := card_erase_add_one ((G.mem_neighborFinset a r).mpr hra.symm)
  have hx' := card_erase_add_one ((G.mem_neighborFinset x a).mpr hax.symm)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at ha hx'
  have hda := hΔ a
  have hdx := hΔ x
  omega

theorem no_zero_of_four_labels (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) {r : V} (hs : (labels Q r).card = 4) :
    zeroTips Q r = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxU,hxt⟩ := mem_filter.mp hx
  obtain ⟨hxQ,hxr,hrx⟩ := (mem_outerSupport Q r x).mp hxU
  obtain ⟨y,hxy,hxyQ⟩ := selected_neighbor Q hxQ
  have hyr : y ≠ r := by intro h; subst y; exact hrx hxy.symm
  have hry : ¬ G.Adj r y := by
    intro h
    have : y ∈ tip G r x := (mem_tip r x y).mpr ⟨hxy,h⟩
    simpa [hxt] using this
  have hcov := outer_cover Q hQ hxr hyr hrx hry hxy hxyQ
  rw [hxt, empty_union] at hcov
  have hfour := card_le_card hcov
  rw [hs] at hfour
  have hnot : x ∉ tip G r y := by simp [mem_tip, hrx]
  have hsub : insert x (tip G r y) ⊆ G.neighborFinset y := by
    intro v hv
    rcases mem_insert.mp hv with h | h
    · subst v; simpa using hxy.symm
    · exact mem_of_mem_inter_left h
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hnot, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hd := hΔ y
  omega

theorem few_support_edges (Q : Finset G.edgeSet) (M : Finset V) (hM : M.card ≤ 2)
    (hs : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ M) : Q.card ≤ 2 := by
  have hcov : ∀ e ∈ Q, ∃ x ∈ e.val, x ∈ M := by
    rintro ⟨e,heG⟩ he
    induction e using Sym2.ind with
    | _ x y => exact ⟨x,by simp,hs _ he x (by simp)⟩
  have hc := selected_cover_bound Q M hcov
  have hsum := sum_le_sum (s := M) (f := fun x => (selectedAt Q x).card)
    (g := fun _ => 1) (by
      intro x hx
      have hsub : labels Q x ⊆ M.erase x := by
        intro y hy
        obtain ⟨hxy,heQ⟩ := (mem_labels Q x y).mp hy
        exact mem_erase.mpr ⟨hxy.ne.symm,hs _ heQ y (by simp)⟩
      have h := card_le_card hsub
      rw [labels_card,card_erase_of_mem hx] at h
      omega)
  simp only [sum_const,smul_eq_mul,mul_one] at hsum
  omega

theorem independent_root_support_le_nine (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hq : 16 ≤ Q.card)
    {r : V} (hs : 3 ≤ (labels Q r).card)
    (hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b) :
    (outerSupport Q r).card ≤ 9 := by
  by_contra! hn
  have hp := root_partition_bound Q r hA
  have ht := type_budget hΔ Q r
  have htr := triple_budget Q r
  have hz := zero_le_triple hΔ Q hQ hs
  have ho := outer_budget hΔ Q hQ hs
  have hsl : (labels Q r).card ≤ 4 :=
    (card_le_card (filter_subset _ _)).trans (by simpa using hΔ r)
  by_cases hsingle : ∃ x ∈ selectedTips Q r, (tip G r x).card = 1
  · obtain ⟨x,hx,hxt⟩ := hsingle
    have hb := single_tip_bound hΔ Q hQ hA hx hxt
    have hk := cross_budget Q r
    have hs4 : (labels Q r).card = 4 := by omega
    have hz0 := no_zero_of_four_labels hΔ Q hQ hs4
    rw [hz0,card_empty] at ht hz
    have he2 : excess Q r = 2 := by omega
    have hT0 : (tripleTips Q r).card = 0 := by omega
    have ho4 : 4 ≤ (outerSelected Q r).card := by omega
    have hty (y : V) (hy : y ∈ outerSupport Q r) : (tip G r y).card ≤ 2 := by
      have hnot : y ∉ tripleTips Q r := by rw [card_eq_zero.mp hT0]; simp
      have hn3 : ¬ 3 ≤ (tip G r y).card := fun h => hnot (mem_filter.mpr ⟨hy,h⟩)
      omega
    let M := (outerSupport Q r).filter (fun y => 2 ≤ (tip G r y).card)
    have hM : M.card ≤ 2 := by
      have h := sum_le_sum (s := outerSupport Q r)
        (f := fun y => if 2 ≤ (tip G r y).card then 1 else 0)
        (g := fun y => (tip G r y).card - 1) (by intro y hy; split_ifs <;> omega)
      simp only [← card_filter] at h
      change M.card ≤ excess Q r at h
      omega
    have hOM : ∀ e ∈ outerSelected Q r, ∀ y ∈ e.val, y ∈ M := by
      rintro ⟨e,heG⟩ he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨heQ,hU⟩ := mem_filter.mp he
        have haU := hU a (by simp)
        have hbU := hU b (by simp)
        have ha := (mem_outerSupport Q r a).mp haU
        have hb := (mem_outerSupport Q r b).mp hbU
        have hc := card_le_card (outer_cover Q hQ ha.2.1 hb.2.1 ha.2.2 hb.2.2 heG heQ)
        have hu := card_union_le (tip G r a) (tip G r b)
        have hta := hty a haU
        have htb := hty b hbU
        intro y hy
        rcases Sym2.mem_iff.mp hy with h | h
        · subst y; exact mem_filter.mpr ⟨haU,by omega⟩
        · subst y; exact mem_filter.mpr ⟨hbU,by omega⟩
    have hf := few_support_edges (outerSelected Q r) M hM hOM
    omega
  · have hk := cross_budget_no_single Q r (by
      intro x hx hxt
      exact hsingle ⟨x,hx,hxt⟩)
    omega

theorem type_identity (Q : Finset G.edgeSet) (r : V) :
    (outerSupport Q r).card + excess Q r =
      (∑ x ∈ outerSupport Q r, (tip G r x).card) + (zeroTips Q r).card := by
  have hp (x : V) : 1 + ((tip G r x).card - 1) =
      (tip G r x).card + if tip G r x = ∅ then 1 else 0 := by
    by_cases ht : tip G r x = ∅
    · simp [ht]
    · have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr ht)
      simp only [ht, ite_false, add_zero]
      omega
  have h := sum_congr (s₁ := outerSupport Q r) rfl (fun x _ => hp x)
  simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one,
    ← card_filter, excess, zeroTips] using h

theorem type_sum_le_ten_of_internal (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) {r a b : V} (hra : G.Adj r a) (hrb : G.Adj r b)
    (hab : G.Adj a b) : ∑ x ∈ outerSupport Q r, (tip G r x).card ≤ 10 := by
  let U := outerSupport Q r
  let C (v : V) := U.filter (G.Adj v)
  have heq : (∑ x ∈ U, (tip G r x).card) = ∑ v ∈ G.neighborFinset r, (C v).card := by
    have ht (x : V) : (tip G r x).card =
        ∑ v ∈ G.neighborFinset r, if G.Adj v x then 1 else 0 := by
      rw [← card_filter]
      congr 1
      ext v
      simp [tip,G.adj_comm,and_comm]
    simp_rw [ht, C, card_filter]
    exact sum_comm
  have hcol (v : V) (hv : G.Adj r v) : (C v).card ≤ 3 := by
    have hsub : insert r (C v) ⊆ G.neighborFinset v := by
      intro x hx
      rcases mem_insert.mp hx with h | h
      · subst x; simpa using hv.symm
      · simpa using (mem_filter.mp h).2
    have hr : r ∉ C v := by simp [C,U,outerSupport]
    have hc := card_le_card hsub
    rw [card_insert_of_notMem hr,SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hΔ v
    omega
  have htwo (v w : V) (hv : G.Adj r v) (hw : G.Adj r w) (hvw : G.Adj v w) :
      (C v).card ≤ 2 := by
    have hsub : insert r (insert w (C v)) ⊆ G.neighborFinset v := by
      intro x hx
      rcases mem_insert.mp hx with h | h
      · subst x; simpa using hv.symm
      rcases mem_insert.mp h with h | h
      · subst x; simpa using hvw
      · simpa using (mem_filter.mp h).2
    have hwC : w ∉ C v := by
      intro h
      exact ((mem_outerSupport Q r w).mp (mem_filter.mp h).1).2.2 hw
    have hrC : r ∉ C v := by simp [C,U,outerSupport]
    have hrW : r ∉ insert w (C v) := by simp [hw.ne,hrC]
    have hc := card_le_card hsub
    rw [card_insert_of_notMem hrW,card_insert_of_notMem hwC,
      SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hΔ v
    omega
  have ha2 := htwo a b hra hrb hab
  have hb2 := htwo b a hrb hra hab.symm
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (f := fun v => (C v).card + (if v = a then 1 else 0) + (if v = b then 1 else 0))
    (g := fun _ => 3) (by
      intro v hv
      have hc := hcol v ((G.mem_neighborFinset r v).mp hv)
      by_cases hva : v = a <;> by_cases hvb : v = b <;> simp_all <;> omega)
  simp only [sum_add_distrib] at hsum
  simp only [sum_ite_eq',SimpleGraph.mem_neighborFinset,hra,hrb,ite_true,
    sum_const,smul_eq_mul,SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hd := hΔ r
  change (∑ x ∈ U, (tip G r x).card) ≤ 10
  rw [heq]
  omega

theorem nonindependent_root_support_le_nine (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hq : 16 ≤ Q.card)
    {r : V} (hs : 3 ≤ (labels Q r).card)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) :
    (outerSupport Q r).card ≤ 9 := by
  by_contra! hn
  have hsum := type_sum_le_ten_of_internal hΔ Q hra hrb hab
  have hi := type_identity Q r
  have hz := zero_le_triple hΔ Q hQ hs
  have ht := triple_budget Q r
  have he0 : excess Q r = 0 := by omega
  have hty (x : V) (hx : x ∈ outerSupport Q r) : (tip G r x).card ≤ 1 := by
    have h := single_le_sum (f := fun y => (tip G r y).card - 1)
      (fun y _ => Nat.zero_le _) hx
    change _ ≤ excess Q r at h
    omega
  have htouch : ∀ e ∈ Q, ∃ x ∈ e.val, G.Adj r x := by
    rintro ⟨e,heG⟩ heQ
    induction e using Sym2.ind with
    | _ x y =>
      by_cases hrx : G.Adj r x
      · exact ⟨x,by simp,hrx⟩
      by_cases hry : G.Adj r y
      · exact ⟨y,by simp,hry⟩
      have hxr : x ≠ r := by intro h; subst x; exact hry heG
      have hyr : y ≠ r := by intro h; subst y; exact hrx heG.symm
      have hxU : x ∈ outerSupport Q r := (mem_outerSupport Q r x).mpr
        ⟨(mem_endpoints Q x).mpr ⟨_,heQ,by simp⟩,hxr,hrx⟩
      have hyU : y ∈ outerSupport Q r := (mem_outerSupport Q r y).mpr
        ⟨(mem_endpoints Q y).mpr ⟨_,heQ,by simp⟩,hyr,hry⟩
      have hc := card_le_card (outer_cover Q hQ hxr hyr hrx hry heG heQ)
      have hu := card_union_le (tip G r x) (tip G r y)
      have htx := hty x hxU
      have hty' := hty y hyU
      omega
  have hc : Q.card ≤ (touchingEdges G (G.neighborFinset r)).card := by
    apply card_le_card_of_injOn (fun e : G.edgeSet => e.val)
    · intro e he
      obtain ⟨x,hxe,hrx⟩ := htouch e he
      exact mem_filter.mpr ⟨G.mem_edgeFinset.mpr e.property,x,hxe,by simpa using hrx⟩
    · exact fun _ _ _ _ h => Subtype.ext h
  have hp : 1 ≤ (internalEdges G (G.neighborFinset r)).card := by
    apply card_pos.mpr
    refine ⟨s(a,b),mem_filter.mpr ⟨G.mem_edgeFinset.mpr hab,?_⟩⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with h | h
    · subst x; simpa using hra
    · subst x; simpa using hrb
  have hd := region_degree_sum G (G.neighborFinset r)
  have hu := sum_le_sum (s := G.neighborFinset r) (fun x _ => hΔ x)
  simp only [sum_const,smul_eq_mul,SimpleGraph.card_neighborFinset_eq_degree] at hu
  have hr := hΔ r
  omega

/-- Improved support bound; no local rim condition is needed. -/
theorem endpoint_bound_14 (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hsize : 16 ≤ Q.card) : (endpoints Q).card ≤ 14 := by
  obtain ⟨r,hs⟩ := exists_three_labels hΔ Q hQ (by omega)
  have ho : (outerSupport Q r).card ≤ 9 := by
    by_cases hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b
    · exact independent_root_support_le_nine hΔ Q hQ hsize hs hA
    · push Not at hA
      obtain ⟨a,b,hra,hrb,hab⟩ := hA
      exact nonindependent_root_support_le_nine hΔ Q hQ hsize hs hra hrb hab
  have hc := card_sdiff_add_card_inter (endpoints Q) (insert r (G.neighborFinset r))
  have hi := card_le_card (inter_subset_right :
    endpoints Q ∩ insert r (G.neighborFinset r) ⊆ insert r (G.neighborFinset r))
  have hn := card_insert_le r (G.neighborFinset r)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hn
  have hd := hΔ r
  change (endpoints Q \ insert r (G.neighborFinset r)).card ≤ 9 at ho
  omega

#print axioms endpoint_bound_14

end Se20Fractional.ThirdPass
