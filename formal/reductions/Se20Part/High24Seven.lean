import Se20Part.LegacyBridge

noncomputable section
open scoped Classical
open Finset
namespace Se20Part
open Legacy
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G)
include hΔ

theorem high24_opposite_star_adj {u v a x b : V} (e f g : G.edgeSet)
    (he : e.val = s(u,v)) (hf : f.val = s(a,x)) (hg : g.val = s(v,b))
    (he24 : (Legacy.conflictGraph G).degree e = 24)
    (hf24 : (Legacy.conflictGraph G).degree f = 24)
    (hua : G.Adj u a) (hav : a ≠ v) (hxu : x ≠ u) (hbu : b ≠ u)
    (hfg : Legacy.StrongConflict G f g) : G.Adj x b := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  have hvb : G.Adj v b := G.mem_edgeSet.mp (hg ▸ g.prop)
  have hax : G.Adj a x := G.mem_edgeSet.mp (hf ▸ f.prop)
  have hnav : ¬ G.Adj a v :=
    endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he he24 hua huv hav
  have hnab : ¬ G.Adj a b := no_cross_edge_of_degree_eq_24 G hΔ e he he24
    (by simp [hav,hua]) (by simp [hbu,hvb])
  have hnxv : ¬ G.Adj x v := by
    intro hxv
    exact no_cross_edge_of_degree_eq_24 G hΔ f hf hf24
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

theorem high24_joint_side_star (Q : Finset G.edgeSet)
    (hQ : (Legacy.conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, (Legacy.conflictGraph G).degree e = 24)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u,v)) :
    (((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)).card +
      (branchEdges G Q u v).card ≤ 3 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  let A := ((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)
  let T := branchEdges G Q u v
  have hA : A.card ≤ 3 := high24_side_card_le_three G hΔ Q hQ h24 huv
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
      exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he (h24 e heQ)
        hua huv hav hav'
    exact high24_opposite_star_adj G hΔ e f g he hfa hgb (h24 e heQ) (h24 f hfQ)
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
      exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he (h24 e heQ)
        hua huv hav hav'
    exact no_cross_edge_of_degree_eq_24 G hΔ g hgb (h24 g hgQ)
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
        exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he (h24 e heQ)
          hua huv hav hva.symm
      exact no_cross_edge_of_degree_eq_24 G hΔ f hfa (h24 f hfQ)
        (by simp [hxy,hay]) (by simp [hba,hxb]) hyb
    · have hxy := high24_external_conflict_adj G hΔ f l hfa hlc
        (h24 f hfQ) (h24 l hlQ) hua huc hac hxu hyu (hQ hfQ hlQ hfl)
      exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ f
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

/-- G08, with ambient degree exactly 24 and no global girth assumption. -/
theorem high24_clique_seven (Q : Finset G.edgeSet)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, (L2 G).degree e = 24) : Q.card ≤ 7 := by
  have hQL : (Legacy.conflictGraph G).IsClique (Q : Set G.edgeSet) := by
    simpa only [legacy_conflictGraph_eq] using hQ
  have h24L : ∀ e ∈ Q, (Legacy.conflictGraph G).degree e = 24 := by
    intro e he
    have hh := h24 e he
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hh ⊢
    simpa only [legacy_conflictGraph_eq] using hh
  by_cases hqe : Q = ∅
  · simp [hqe]
  obtain ⟨e,heQ⟩ := nonempty_iff_ne_empty.mpr hqe
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  let A := ((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)
  let B := ((G.neighborFinset v).erase u).biUnion (branchEdges G Q v)
  let U := branchEdges G Q v u
  let T := branchEdges G Q u v
  have hside := high24_joint_side_star G hΔ Q hQL h24L e heQ he
  have hside' := high24_joint_side_star G hΔ Q hQL h24L e heQ (he.trans Sym2.eq_swap)
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

end Se20Part
