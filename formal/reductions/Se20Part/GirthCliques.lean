import Se20Part.GirthDegree
import Se20Part.High24Seven

noncomputable section
open scoped Classical BigOperators
open Finset
namespace Se20Part.GirthClique
open Legacy
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G)

include hΔ in
theorem girth_endpoint_independent (e : G.edgeSet) {u v a b : V}
    (_he : e.val = s(u,v)) (hg : 5 ≤ G.egirth)
    (hua : G.Adj u a) (hub : G.Adj u b) (_hab : a ≠ b) : ¬ G.Adj a b := by
  intro hab
  exact GirthFive.no_triangle hg hua hab hub.symm

include hΔ in
theorem girth_no_cross (e : G.edgeSet) {u v a b : V}
    (he : e.val = s(u,v)) (hg : 5 ≤ G.egirth)
    (ha : a ∈ (G.neighborFinset u).erase v)
    (hb : b ∈ (G.neighborFinset v).erase u) : ¬ G.Adj a b := by
  intro hab
  have huv := G.mem_edgeSet.mp (he ▸ e.prop)
  have hua := (G.mem_neighborFinset _ _).mp (mem_erase.mp ha).2
  have hvb := (G.mem_neighborFinset _ _).mp (mem_erase.mp hb).2
  rcases GirthFive.square_backtrack hg hua hab hvb.symm huv.symm with h|h
  · exact (mem_erase.mp hb).1 h.symm
  · exact (mem_erase.mp ha).1 h

/-- With girth at least five, an edge cannot join two neighbours of a common vertex. -/
theorem girth_edge_not_between_neighbors
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b : V} (e : G.edgeSet)
    (he : e.val = s(a, b)) (h24 : 5 ≤ G.egirth)
    (hua : G.Adj u a) (hub : G.Adj u b) : False := by
  have hab : G.Adj a b := G.mem_edgeSet.mp (he ▸ e.property)
  exact girth_endpoint_independent G hΔ e he h24
    hua.symm hab hub.ne hub

/-- Conflicting edges from distinct branches must have adjacent outer
endpoints. All other conflict witnesses are excluded by the girth condition. -/
theorem girth_external_conflict_adj
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b x y : V} (e f : G.edgeSet)
    (he : e.val = s(a, x)) (hf : f.val = s(b, y))
    (he24 : 5 ≤ G.egirth)
    (hf24 : 5 ≤ G.egirth)
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (hxu : x ≠ u) (hyu : y ≠ u) (hc : StrongConflict G e f) : G.Adj x y := by
  have hnab : ¬ G.Adj a b := by
    intro h
    exact girth_endpoint_independent G hΔ e he he24
      hua.symm h hub.ne hub
  have hnxb : ¬ G.Adj x b := by
    intro h
    exact girth_no_cross G hΔ e he he24
      (mem_erase.mpr ⟨hxu.symm, (G.mem_neighborFinset a u).mpr hua.symm⟩)
      (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset x b).mpr h⟩) hub
  have hnay : ¬ G.Adj a y := by
    intro h
    exact girth_no_cross G hΔ f hf hf24
      (mem_erase.mpr ⟨hyu.symm, (G.mem_neighborFinset b u).mpr hub.symm⟩)
      (mem_erase.mpr ⟨hab, (G.mem_neighborFinset y a).mpr h.symm⟩) hua
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he hc
  rw [hf, Sym2.mem_iff] at hwf
  rcases hwf with hwb | hwy
  · have hb : b ∈ endpointNeighbourCover G a x := hwb ▸ hw
    rcases mem_union.mp hb with h | h
    · exact (hnab ((G.mem_neighborFinset a b).mp (mem_erase.mp h).2)).elim
    · exact (hnxb ((G.mem_neighborFinset x b).mp (mem_erase.mp h).2)).elim
  · have hy : y ∈ endpointNeighbourCover G a x := hwy ▸ hw
    rcases mem_union.mp hy with h | h
    · exact (hnay ((G.mem_neighborFinset a y).mp (mem_erase.mp h).2)).elim
    · exact (G.mem_neighborFinset x y).mp (mem_erase.mp h).2

theorem girth_distinct_branches_ne
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b : V} (e f : G.edgeSet)
    (he24 : 5 ≤ G.egirth)
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (ha : a ∈ e.val) (hb : b ∈ f.val) : e ≠ f := by
  intro hef
  have hb' : b ∈ e.val := hef ▸ hb
  exact girth_edge_not_between_neighbors G hΔ e
    ((Sym2.mem_and_mem_iff hab).mp ⟨ha, hb'⟩) he24 hua hub

/-- Two edges in one branch exclude any edge in a different branch of the
same centre, provided the edges form a clique and the girth is at least five. -/
theorem girth_mixed_branches_cannot_have_fork
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth)
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (e₁ e₂ f : G.edgeSet) (h₁ : e₁ ∈ branchEdges G Q u a)
    (h₂ : e₂ ∈ branchEdges G Q u a) (hf : f ∈ branchEdges G Q u b)
    (hne : e₁ ≠ e₂) : False := by
  obtain ⟨h₁Q, h₁a, h₁u⟩ := (mem_branchEdges G Q u a e₁).mp h₁
  obtain ⟨h₂Q, h₂a, h₂u⟩ := (mem_branchEdges G Q u a e₂).mp h₂
  obtain ⟨hfQ, hfb, hfu⟩ := (mem_branchEdges G Q u b f).mp hf
  obtain ⟨x₁, hx₁⟩ := Sym2.mem_iff_exists.mp h₁a
  obtain ⟨x₂, hx₂⟩ := Sym2.mem_iff_exists.mp h₂a
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hfb
  have hx₁u : x₁ ≠ u := by
    intro h
    apply h₁u
    rw [hx₁, h]
    exact Sym2.mem_mk_right _ _
  have hx₂u : x₂ ≠ u := by
    intro h
    apply h₂u
    rw [hx₂, h]
    exact Sym2.mem_mk_right _ _
  have hyu : y ≠ u := by
    intro h
    apply hfu
    rw [hy, h]
    exact Sym2.mem_mk_right _ _
  have h₁f := girth_distinct_branches_ne G hΔ e₁ f (h24 e₁ h₁Q) hua hub hab h₁a hfb
  have h₂f := girth_distinct_branches_ne G hΔ e₂ f (h24 e₂ h₂Q) hua hub hab h₂a hfb
  have hxy₁ := girth_external_conflict_adj G hΔ e₁ f hx₁ hy
    (h24 e₁ h₁Q) (h24 f hfQ) hua hub hab hx₁u hyu (hQ h₁Q hfQ h₁f)
  have hxy₂ := girth_external_conflict_adj G hΔ e₂ f hx₂ hy
    (h24 e₂ h₂Q) (h24 f hfQ) hua hub hab hx₂u hyu (hQ h₂Q hfQ h₂f)
  have hx₂₁ : x₂ ≠ x₁ := by
    intro h
    apply hne
    apply Subtype.ext
    rw [h] at hx₂
    exact hx₁.trans hx₂.symm
  have hya : y ≠ a := by
    intro h
    exact girth_edge_not_between_neighbors G hΔ f
      (by simpa only [h] using hy) (h24 f hfQ) hub hua
  have hax₂ : G.Adj a x₂ := G.mem_edgeSet.mp (hx₂ ▸ e₂.property)
  exact girth_no_cross G hΔ e₁ hx₁ (h24 e₁ h₁Q)
    (mem_erase.mpr ⟨hx₂₁, (G.mem_neighborFinset a x₂).mpr hax₂⟩)
    (mem_erase.mpr ⟨hya, (G.mem_neighborFinset x₁ y).mpr hxy₁⟩) hxy₂

/-- At most three occupied branches, each of capacity three, contribute at
most three edges in total: a branch with two edges excludes all others. -/
theorem girth_branch_union_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth)
    (u : V) (A : Finset V) (hA : A.card ≤ 3)
    (hAu : ∀ a ∈ A, G.Adj u a) :
    (A.biUnion (branchEdges G Q u)).card ≤ 3 := by
  classical
  by_cases hbig : ∃ a ∈ A, 1 < (branchEdges G Q u a).card
  · obtain ⟨a, ha, hbig⟩ := hbig
    obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := one_lt_card.mp hbig
    have hs : A.biUnion (branchEdges G Q u) ⊆ branchEdges G Q u a := by
      intro f hf
      obtain ⟨b, hb, hfb⟩ := mem_biUnion.mp hf
      by_cases hba : b = a
      · simpa only [hba] using hfb
      · exact (girth_mixed_branches_cannot_have_fork G hΔ Q hQ h24
          (hAu a ha) (hAu b hb) (Ne.symm hba) e₁ e₂ f h₁ h₂ hfb hne).elim
    exact (card_le_card hs).trans (branchEdges_card_le_three G hΔ Q (hAu a ha))
  · have hsmall : ∀ a ∈ A, (branchEdges G Q u a).card ≤ 1 := by
      intro a ha
      by_contra hn
      exact hbig ⟨a, ha, by omega⟩
    have hs := sum_le_sum (s := A) hsmall
    simp only [sum_const, smul_eq_mul, mul_one] at hs
    exact (card_biUnion_le.trans hs).trans hA

/-- One side of a fixed original edge has at most three external clique
edges. The fixed edge need not itself belong to the clique. -/
theorem girth_side_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth)
    {u v : V} (huv : G.Adj u v) :
    (((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)).card ≤ 3 := by
  have hcard := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hd := hΔ u
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact girth_branch_union_card_le_three G hΔ Q hQ h24 u _ (by omega)
    (fun a ha => (G.mem_neighborFinset u a).mp (mem_erase.mp ha).2)


include hΔ
theorem girth_opposite_star_adj {u v a x b : V} (e f g : G.edgeSet)
    (he : e.val = s(u,v)) (hf : f.val = s(a,x)) (hg : g.val = s(v,b))
    (he24 : 5 ≤ G.egirth)
    (hf24 : 5 ≤ G.egirth)
    (hua : G.Adj u a) (hav : a ≠ v) (hxu : x ≠ u) (hbu : b ≠ u)
    (hfg : Legacy.StrongConflict G f g) : G.Adj x b := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  have hvb : G.Adj v b := G.mem_edgeSet.mp (hg ▸ g.prop)
  have hax : G.Adj a x := G.mem_edgeSet.mp (hf ▸ f.prop)
  have hnav : ¬ G.Adj a v :=
    girth_endpoint_independent G hΔ e he he24 hua huv hav
  have hnab : ¬ G.Adj a b := girth_no_cross G hΔ e he he24
    (by simp [hav,hua]) (by simp [hbu,hvb])
  have hnxv : ¬ G.Adj x v := by
    intro hxv
    exact girth_no_cross G hΔ f hf hf24
      (by simp [hxu.symm,hua.symm]) (by simp [hav.symm,hxv]) huv
  obtain ⟨w,hw,hwg⟩ := strongConflict_meets_cover G hf hfg
  rw [hg,Sym2.mem_iff] at hwg
  rcases hwg with rfl | rfl
  · rcases mem_union.mp hw with hw | hw
    · exact (hnav ((G.mem_neighborFinset _ _).mp (mem_erase.mp hw).2)).elim
    · exact (hnxv ((G.mem_neighborFinset _ _).mp (mem_erase.mp hw).2)).elim
  · rcases mem_union.mp hw with hw | hw
    · exact (hnab ((G.mem_neighborFinset _ _).mp (mem_erase.mp hw).2)).elim
    · exact (G.mem_neighborFinset _ _).mp (mem_erase.mp hw).2

theorem girth_joint_side_star (Q : Finset G.edgeSet)
    (hQ : (Legacy.conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u,v)) :
    (((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)).card +
      (branchEdges G Q u v).card ≤ 3 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  let A := ((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)
  let T := branchEdges G Q u v
  have hA : A.card ≤ 3 := girth_side_card_le_three G hΔ Q hQ h24 huv
  have hT : T.card ≤ 3 := branchEdges_card_le_three G hΔ Q huv
  have unpackA (f : G.edgeSet) (hf : f ∈ A) :
      ∃ a x, f.val = s(a,x) ∧ G.Adj u a ∧ a ≠ v ∧ x ≠ u ∧ f ∈ Q := by
    obtain ⟨a,ha,hfa⟩ := mem_biUnion.mp hf
    obtain ⟨hfQ,haf,huf⟩ := (mem_branchEdges G Q u a f).mp hfa
    obtain ⟨x,hfx⟩ := Sym2.mem_iff_exists.mp haf
    refine ⟨a,x,hfx,(G.mem_neighborFinset _ _).mp (mem_erase.mp ha).2,
      (mem_erase.mp ha).1,?_,hfQ⟩
    intro h
    exact huf (hfx ▸ h ▸ Sym2.mem_mk_right a x)
  have unpackT (g : G.edgeSet) (hgT : g ∈ T) :
      ∃ b, g.val = s(v,b) ∧ b ≠ u ∧ g ∈ Q := by
    obtain ⟨hgQ,hvg,hug⟩ := (mem_branchEdges G Q u v g).mp hgT
    obtain ⟨b,hgb⟩ := Sym2.mem_iff_exists.mp hvg
    refine ⟨b,hgb,?_,hgQ⟩
    intro h
    exact hug (hgb ▸ h ▸ Sym2.mem_mk_right v b)
  have hcross (f : G.edgeSet) (hf : f ∈ A) (g : G.edgeSet) (hgT : g ∈ T)
      {a x b : V} (hfa : f.val = s(a,x)) (hgb : g.val = s(v,b))
      (hua : G.Adj u a) (hav : a ≠ v) (hxu : x ≠ u) (hbu : b ≠ u)
      (hfQ : f ∈ Q) (hgQ : g ∈ Q) : G.Adj x b := by
    have hfg : f ≠ g := by
      intro h
      have hav' : G.Adj a v := G.mem_edgeSet.mp
        ((Sym2.mem_and_mem_iff hav).mp ⟨hfa ▸ Sym2.mem_mk_left a x,
          h ▸ hgb ▸ Sym2.mem_mk_left v b⟩ ▸ f.prop)
      exact girth_endpoint_independent G hΔ e he (h24 e heQ)
        hua huv hav hav'
    exact girth_opposite_star_adj G hΔ e f g he hfa hgb (h24 e heQ) (h24 f hfQ)
      hua hav hxu hbu (hQ hfQ hgQ hfg)
  have htwoT : 0 < A.card → T.card ≤ 1 := by
    intro ha
    by_contra ht
    obtain ⟨f,hf⟩ := card_pos.mp ha
    obtain ⟨g,hg,l,hl,hgl⟩ := one_lt_card.mp (by omega : 1 < T.card)
    obtain ⟨a,x,hfa,hua,hav,hxu,hfQ⟩ := unpackA f hf
    obtain ⟨b,hgb,hbu,hgQ⟩ := unpackT g hg
    obtain ⟨c,hlc,hcu,hlQ⟩ := unpackT l hl
    have hxb := hcross f hf g hg hfa hgb hua hav hxu hbu hfQ hgQ
    have hxc := hcross f hf l hl hfa hlc hua hav hxu hcu hfQ hlQ
    have hcb : c ≠ b := fun h => hgl (Subtype.ext (hgb.trans (h ▸ hlc).symm))
    have hvc : G.Adj v c := G.mem_edgeSet.mp (hlc ▸ l.prop)
    have hxv : x ≠ v := by
      intro h
      have hav' : G.Adj a v := G.mem_edgeSet.mp ((h ▸ hfa) ▸ f.prop)
      exact girth_endpoint_independent G hΔ e he (h24 e heQ)
        hua huv hav hav'
    exact girth_no_cross G hΔ g hgb (h24 g hgQ)
      (by simp [hcb,hvc]) (by simp [hxv,hxb.symm]) hxc.symm
  have htwoA : 0 < T.card → A.card ≤ 1 := by
    intro ht
    by_contra ha
    obtain ⟨g,hg⟩ := card_pos.mp ht
    obtain ⟨f,hf,l,hl,hfl⟩ := one_lt_card.mp (by omega : 1 < A.card)
    obtain ⟨a,x,hfa,hua,hav,hxu,hfQ⟩ := unpackA f hf
    obtain ⟨c,y,hlc,huc,hcv,hyu,hlQ⟩ := unpackA l hl
    obtain ⟨b,hgb,hbu,hgQ⟩ := unpackT g hg
    have hxb := hcross f hf g hg hfa hgb hua hav hxu hbu hfQ hgQ
    have hyb := hcross l hl g hg hlc hgb huc hcv hyu hbu hlQ hgQ
    by_cases hac : a = c
    · subst c
      have hxy : y ≠ x := fun h => hfl (Subtype.ext (hfa.trans (h ▸ hlc).symm))
      have hay : G.Adj a y := G.mem_edgeSet.mp (hlc ▸ l.prop)
      have hba : b ≠ a := by
        intro h
        have hva : G.Adj v a := G.mem_edgeSet.mp ((h ▸ hgb) ▸ g.prop)
        exact girth_endpoint_independent G hΔ e he (h24 e heQ)
          hua huv hav hva.symm
      exact girth_no_cross G hΔ f hfa (h24 f hfQ)
        (by simp [hxy,hay]) (by simp [hba,hxb]) hyb
    · have hxy := girth_external_conflict_adj G hΔ f l hfa hlc
        (h24 f hfQ) (h24 l hlQ) hua huc hac hxu hyu (hQ hfQ hlQ hfl)
      exact girth_endpoint_independent G hΔ f
        (hfa.trans Sym2.eq_swap) (h24 f hfQ) hxb hxy hyb.ne.symm hyb.symm
  by_cases ha : A.card = 0
  · change A.card + T.card ≤ 3
    omega
  by_cases ht : T.card = 0
  · change A.card + T.card ≤ 3
    omega
  have := htwoT (by omega)
  have := htwoA (by omega)
  change A.card + T.card ≤ 3
  omega

/-- F01, the seven-edge bound at girth at least five. -/
theorem girth_clique_seven (hg : 5 ≤ G.egirth) (Q : Finset G.edgeSet)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) : Q.card ≤ 7 := by
  have hQL : (Legacy.conflictGraph G).IsClique (Q : Set G.edgeSet) := by
    simpa only [legacy_conflictGraph_eq] using hQ
  have h24L : ∀ e ∈ Q, 5 ≤ G.egirth := fun _ _ => hg
  by_cases hqe : Q = ∅
  · simp [hqe]
  obtain ⟨e,heQ⟩ := nonempty_iff_ne_empty.mpr hqe
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  let A := ((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)
  let B := ((G.neighborFinset v).erase u).biUnion (branchEdges G Q v)
  let U := branchEdges G Q v u
  let T := branchEdges G Q u v
  have hside := girth_joint_side_star G hΔ Q hQL h24L e heQ he
  have hside' := girth_joint_side_star G hΔ Q hQL h24L e heQ (he.trans Sym2.eq_swap)
  have hcover : Q ⊆ insert e ((A ∪ T) ∪ (B ∪ U)) := by
    intro f hf
    by_cases hfe : f = e
    · simp [hfe]
    apply mem_insert_of_mem
    by_cases hu : u ∈ f.val
    · have hv : v ∉ f.val := fun hv => hfe (Subtype.ext
        (((Sym2.mem_and_mem_iff huv.ne).mp ⟨hu,hv⟩).trans he.symm))
      exact mem_union_right _ (mem_union_right _ ((mem_branchEdges G Q v u f).mpr ⟨hf,hu,hv⟩))
    by_cases hv : v ∈ f.val
    · exact mem_union_left _ (mem_union_right _ ((mem_branchEdges G Q u v f).mpr ⟨hf,hv,hu⟩))
    obtain ⟨w,hw,hwf⟩ := strongConflict_meets_cover G he (hQL heQ hf (Ne.symm hfe))
    rcases mem_union.mp hw with hw | hw
    · exact mem_union_left _ (mem_union_left _
        (mem_biUnion.mpr ⟨w,hw,(mem_branchEdges G Q u w f).mpr ⟨hf,hwf,hu⟩⟩))
    · exact mem_union_right _ (mem_union_left _
        (mem_biUnion.mpr ⟨w,hw,(mem_branchEdges G Q v w f).mpr ⟨hf,hwf,hv⟩⟩))
  have hc := card_le_card hcover
  have hi := card_insert_le e ((A ∪ T) ∪ (B ∪ U))
  have h1 := card_union_le (A ∪ T) (B ∪ U)
  have h2 := card_union_le A T
  have h3 := card_union_le B U
  change A.card + T.card ≤ 3 at hside
  change B.card + U.card ≤ 3 at hside'
  omega


end Se20Part.GirthClique
