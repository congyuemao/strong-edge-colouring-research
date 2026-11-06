import fourth_pass.RootDegreeThree

namespace Se20Fractional.FourthPass
open Finset DReduction ThirdPass
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A selected edge in a triangle has an edgeless endpoint region. -/
theorem selected_triangle_region_empty (Q : Finset G.edgeSet) (hLow : LocallyLow G Q)
    {r a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b)
    (he : (⟨s(r,a),hra⟩ : G.edgeSet) ∈ Q) :
    internalEdges G (endpointRegion G r a) = ∅ := by
  have hc : 1 ≤ commonCount G r a := by
    apply card_pos.mpr
    exact ⟨b,mem_inter.mpr ⟨by simpa using hrb,by simpa using hab⟩⟩
  have hl := hLow r a hra he
  apply card_eq_zero.mp
  omega

/-- Outside the closed root neighbourhood, any type containing a selected
triangle label must be exactly that singleton. -/
theorem selected_triangle_tip_singleton (Q : Finset G.edgeSet) (hLow : LocallyLow G Q)
    {r a b x : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b)
    (he : (⟨s(r,a),hra⟩ : G.edgeSet) ∈ Q)
    (hxr : x ≠ r) (hrx : ¬ G.Adj r x) (hax : G.Adj a x) :
    tip G r x = {a} := by
  have hempty := selected_triangle_region_empty Q hLow hra hrb hab he
  ext c
  constructor
  · intro hc
    obtain ⟨hxc,hrc⟩ := (mem_tip r x c).mp hc
    apply mem_singleton.mpr
    by_contra hca
    have hxa : x ≠ a := hax.ne.symm
    have hxR : x ∈ endpointRegion G r a :=
      (mem_endpointRegion G r a x).mpr ⟨Or.inr hax,hxr,hxa⟩
    have hcR : c ∈ endpointRegion G r a :=
      (mem_endpointRegion G r a c).mpr ⟨Or.inl hrc,hrc.ne.symm,hca⟩
    have hEdge : s(x,c) ∈ internalEdges G (endpointRegion G r a) := by
      apply mem_filter.mpr
      refine ⟨G.mem_edgeFinset.mpr hxc,?_⟩
      intro y hy
      rcases Sym2.mem_iff.mp hy with rfl | rfl <;> assumption
    simpa [hempty] using hEdge
  · intro hc
    have : c = a := mem_singleton.mp hc
    subst c
    exact (mem_tip r x a).mpr ⟨hax.symm,hra⟩

theorem selected_triangle_outer_empty (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    (hLow : LocallyLow G Q) {r a b : V} (hs : 3 ≤ (labels Q r).card)
    (ha : a ∈ labels Q r) (hb : b ∈ labels Q r) (hab : G.Adj a b) :
    outerSelected Q r = ∅ := by
  obtain ⟨hra,hraQ⟩ := (mem_labels Q r a).mp ha
  obtain ⟨hrb,hrbQ⟩ := (mem_labels Q r b).mp hb
  have hsingle (c d x : V) (hrc : G.Adj r c) (hrd : G.Adj r d) (hcd : G.Adj c d)
      (hcQ : (⟨s(r,c),hrc⟩ : G.edgeSet) ∈ Q) (hx : x ∈ outerSupport Q r)
      (hcx : c ∈ tip G r x) : tip G r x = {c} := by
    obtain ⟨_,hxr,hrx⟩ := (mem_outerSupport Q r x).mp hx
    exact selected_triangle_tip_singleton Q hLow hrc hrd hcd hcQ hxr hrx
      ((mem_tip r x c).mp hcx).1.symm
  have hbound (x y : V) (hx : x ∈ outerSupport Q r) (hy : y ∈ outerSupport Q r)
      (hcov : labels Q r ⊆ tip G r x ∪ tip G r y) (hax : a ∈ tip G r x) : False := by
    have htx := hsingle a b x hra hrb hab hraQ hx hax
    have hby : b ∈ tip G r y := by
      have hb' := hcov hb
      rw [htx] at hb'
      rcases mem_union.mp hb' with h | h
      · exact False.elim (hab.ne (mem_singleton.mp h).symm)
      · exact h
    have hty := hsingle b a y hrb hra hab.symm hrbQ hy hby
    have hc := card_le_card hcov
    have hu := card_union_le (tip G r x) (tip G r y)
    simp only [htx,hty,card_singleton] at hc hu
    omega
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨e,heG⟩ he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨heQ,hU⟩ := mem_filter.mp he
    have hx := (mem_outerSupport Q r x).mp (hU x (by simp))
    have hy := (mem_outerSupport Q r y).mp (hU y (by simp))
    have hc := outer_cover Q hQ hx.2.1 hy.2.1 hx.2.2 hy.2.2 heG heQ
    rcases mem_union.mp (hc ha) with hax | hay
    · exact hbound x y (hU x (by simp)) (hU y (by simp)) hc hax
    · have hc' : labels Q r ⊆ tip G r y ∪ tip G r x := by rwa [union_comm]
      exact hbound y x (hU y (by simp)) (hU x (by simp)) hc' hay

/-- At a root with three selected neighbours, two selected labels cannot be
adjacent in a locally low clique of sixteen or more selected edges. -/
theorem selected_labels_independent (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hLow : LocallyLow G Q)
    (hq : 16 ≤ Q.card) {r : V} (hs : 3 ≤ (labels Q r).card)
    {a b : V} (ha : a ∈ labels Q r) (hb : b ∈ labels Q r) : ¬ G.Adj a b := by
  intro hab
  have ho := selected_triangle_outer_empty Q hQ hLow hs ha hb hab
  obtain ⟨hra,_⟩ := (mem_labels Q r a).mp ha
  obtain ⟨hrb,_⟩ := (mem_labels Q r b).mp hb
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
      have heO : (⟨s(x,y),heG⟩ : G.edgeSet) ∈ outerSelected Q r := by
        refine mem_filter.mpr ⟨heQ,?_⟩
        intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
      simpa [ho] using heO
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
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simpa using (by assumption : G.Adj r _)
  have hd := region_degree_sum G (G.neighborFinset r)
  have hu := sum_le_sum (s := G.neighborFinset r) (fun x _ => hΔ x)
  simp only [sum_const,smul_eq_mul,SimpleGraph.card_neighborFinset_eq_degree] at hu
  have hr := hΔ r
  omega

theorem full_selected_root_independent (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hLow : LocallyLow G Q)
    (hq : 16 ≤ Q.card) {r : V} (hs : 3 ≤ (labels Q r).card)
    (hfull : G.degree r ≤ (labels Q r).card) :
    ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b := by
  have heq : labels Q r = G.neighborFinset r := by
    have hsub : labels Q r ⊆ G.neighborFinset r := filter_subset _ _
    apply eq_of_subset_of_card_le hsub
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hfull
  intro a b ha hb
  apply selected_labels_independent hΔ Q hQ hLow hq hs
  · simpa [heq] using ha
  · simpa [heq] using hb

/-- In the degree-three root case the local hypothesis removes the
independence assumption from the ten-endpoint bound. -/
theorem degree_three_endpoint_le_ten (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hLow : LocallyLow G Q)
    (hq : 16 ≤ Q.card) {r : V} (hs : 3 ≤ (labels Q r).card) (hd : G.degree r = 3) :
    (endpoints Q).card ≤ 10 := by
  exact degree_three_independent_endpoint_le_ten hΔ Q hQ hq hs hd
    (full_selected_root_independent hΔ Q hQ hLow hq hs (by omega))

/-- Once a selected root edge lies in a triangle, that triangle's rim edge
is the only edge in the root neighbourhood. -/
theorem root_internal_singleton (Q : Finset G.edgeSet) (hLow : LocallyLow G Q)
    {r a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b)
    (he : (⟨s(r,a),hra⟩ : G.edgeSet) ∈ Q) :
    internalEdges G (G.neighborFinset r) = {s(a,b)} := by
  have hempty := selected_triangle_region_empty Q hLow hra hrb hab he
  have hl := hLow r a hra he
  have hcommon : (G.neighborFinset r ∩ G.neighborFinset a).card ≤ 1 := by
    change commonCount G r a ≤ 1
    omega
  have hb : b ∈ G.neighborFinset r ∩ G.neighborFinset a := by simp [hrb,hab]
  have huniq (c : V) (hrc : G.Adj r c) (hac : G.Adj a c) : c = b :=
    (card_le_one.mp hcommon) c (by simp [hrc,hac]) b hb
  ext e
  constructor
  · intro heI
    apply mem_singleton.mpr
    obtain ⟨heG,hR⟩ := mem_filter.mp heI
    induction e using Sym2.ind with
    | _ c d =>
      have hcd : G.Adj c d := G.mem_edgeFinset.mp heG
      have hrc : G.Adj r c := by simpa using hR c (by simp)
      have hrd : G.Adj r d := by simpa using hR d (by simp)
      by_cases hca : c = a
      · subst c
        have hdb := huniq d hrd hcd
        subst d
        rfl
      by_cases hda : d = a
      · subst d
        have hcb := huniq c hrc hcd.symm
        subst c
        exact Sym2.eq_swap
      have hcR : c ∈ endpointRegion G r a :=
        (mem_endpointRegion G r a c).mpr ⟨Or.inl hrc,hrc.ne.symm,hca⟩
      have hdR : d ∈ endpointRegion G r a :=
        (mem_endpointRegion G r a d).mpr ⟨Or.inl hrd,hrd.ne.symm,hda⟩
      have he' : s(c,d) ∈ internalEdges G (endpointRegion G r a) := by
        refine mem_filter.mpr ⟨heG,?_⟩
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
      simp [hempty] at he'
  · intro heI
    have heq := mem_singleton.mp heI
    subst e
    refine mem_filter.mpr ⟨G.mem_edgeFinset.mpr hab,?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simpa using (by assumption : G.Adj r _)

theorem root_internal_card_le_one (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hLow : LocallyLow G Q)
    {r : V} (hs : 3 ≤ (labels Q r).card) :
    (internalEdges G (G.neighborFinset r)).card ≤ 1 := by
  by_cases hne : (internalEdges G (G.neighborFinset r)).Nonempty
  · obtain ⟨e,he⟩ := hne
    obtain ⟨heG,hR⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := G.mem_edgeFinset.mp heG
      have hra : G.Adj r a := by simpa using hR a (by simp)
      have hrb : G.Adj r b := by simpa using hR b (by simp)
      have hc : (G.neighborFinset r \ labels Q r).card ≤ 1 := by
        have hd := hΔ r
        have hsub : labels Q r ⊆ G.neighborFinset r := filter_subset _ _
        have hpart : (G.neighborFinset r \ labels Q r).card + (labels Q r).card =
            (G.neighborFinset r).card := card_sdiff_add_card_eq_card hsub
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hpart
        omega
      have haor : a ∈ labels Q r ∨ b ∈ labels Q r := by
        by_contra hn
        push_neg at hn
        have haD : a ∈ G.neighborFinset r \ labels Q r := by simp [hra,hn.1]
        have hbD : b ∈ G.neighborFinset r \ labels Q r := by simp [hrb,hn.2]
        exact hab.ne ((card_le_one.mp hc) a haD b hbD)
      rcases haor with ha | hb
      · obtain ⟨_,heQ⟩ := (mem_labels Q r a).mp ha
        rw [root_internal_singleton Q hLow hra hrb hab heQ]
        simp
      · obtain ⟨_,heQ⟩ := (mem_labels Q r b).mp hb
        rw [root_internal_singleton Q hLow hrb hra hab.symm heQ]
        simp
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

#print axioms selected_labels_independent
#print axioms degree_three_endpoint_le_ten
#print axioms root_internal_card_le_one
end Se20Fractional.FourthPass
