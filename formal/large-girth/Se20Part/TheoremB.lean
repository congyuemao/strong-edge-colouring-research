import Se20Part.LocalDominators

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

theorem EdgeWithin.mono {V : Type*} {G : SimpleGraph V} {k l : ℕ} {e f : G.edgeSet}
    (h : EdgeWithin G k e f) (hkl : k ≤ l) : EdgeWithin G l e f := by
  obtain ⟨x,hx,y,hy,p,hp⟩ := h
  exact ⟨x,hx,y,hy,p,hp.trans hkl⟩

theorem conflict_edgeWithin {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet}
    (h : (L2 G).Adj e f) : EdgeWithin G 1 e f := by
  obtain ⟨_,x,hx,y,hy,hxy⟩ := h
  rcases hxy with rfl | hxy
  · exact ⟨x,hx,x,hy,.nil,by simp⟩
  · exact ⟨x,hx,y,hy,hxy.toWalk,by simp⟩

theorem Separated.inducedMatching {V : Type*} {G : SimpleGraph V} {D : Set G.edgeSet}
    {k : ℕ} (hs : Separated G k D) (hk : 2 ≤ k) : IsInducedMatching D := by
  intro e he f hf hadj
  exact hs e he f hf hadj.1 ((conflict_edgeWithin hadj).mono (by omega))

def WithinFrom {V : Type*} (G : SimpleGraph V) (k : ℕ) (d r : G.edgeSet) : Prop :=
  ∀ x ∈ d.val, ∃ y ∈ r.val, ∃ p : G.Walk x y, p.length ≤ k

theorem layers_within {V : Type*} {G : SimpleGraph V} {r d : G.edgeSet}
    {p t : V} (he : d.val = s(p,t))
    (hp : VertexEdgeDistance G p r 2) (ht : VertexEdgeDistance G t r 3) :
    WithinFrom G 3 d r := by
  intro x hx
  rw [he, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · obtain ⟨y,hy,hpy⟩ := hp.2
    obtain ⟨q,hq⟩ := G.exists_walk_of_edist_eq_coe hpy
    exact ⟨y,hy,q,by omega⟩
  · obtain ⟨y,hy,hty⟩ := ht.2
    obtain ⟨q,hq⟩ := G.exists_walk_of_edist_eq_coe hty
    exact ⟨y,hy,q,by omega⟩

theorem within_conflict_within {V : Type*} {G : SimpleGraph V}
    {r r' d d' : G.edgeSet} {k l : ℕ}
    (hd : WithinFrom G k d r) (hd' : WithinFrom G l d' r')
    (hadj : (L2 G).Adj d d') : EdgeWithin G (k+1+l) r r' := by
  obtain ⟨x,hx,y,hy,p,hp⟩ := conflict_edgeWithin hadj
  obtain ⟨w,hw,q,hq⟩ := hd x hx
  obtain ⟨z,hz,q',hq'⟩ := hd' y hy
  exact ⟨w,hw,z,hz,q.reverse.append (p.append q'), by
    simp only [Walk.length_append, Walk.length_reverse]; omega⟩

theorem layers_avoid_root {V : Type*} {G : SimpleGraph V} {r d : G.edgeSet}
    {p t : V} (he : d.val = s(p,t))
    (hp : VertexEdgeDistance G p r 2) (ht : VertexEdgeDistance G t r 3) :
    ¬ (L2 G).Adj d r := by
  intro h
  obtain ⟨x,hx,y,hy,q,hq⟩ := conflict_edgeWithin h
  have hdist := q.edist_le
  have hq' : (q.length : ℕ∞) ≤ 1 := by exact_mod_cast hq
  have hle := hdist.trans hq'
  rw [he, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · have := (hp.1 y hy).trans hle
    norm_num at this
  · have := (ht.1 y hy).trans hle
    norm_num at this

theorem degree_six_problem {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5)
    {M : Set G.edgeSet} (hm : IsMatching M) (h : M) {r : G.edgeSet}
    (hr : (L2 G).Adj h.val r)
    (hs : Nat.card ((ConflictGraph G M).neighborSet h) = 6) : ProblemAt G M r h.val := by
  have heq := matching_degree_eq_covered_external_nat hg hm h
  have hext : Nat.card (External G h.val) ≤ 6 := by
    simpa only [Nat.card_eq_fintype_card] using external_card_le_six hd h.val
  have hc : Nat.card ↥(External G h.val ∩ Covered M) = 6 := heq.symm.trans hs
  have hsub : External G h.val ∩ Covered M ⊆ External G h.val := Set.inter_subset_left
  have hcard := Set.ncard_le_ncard hsub
  have hext' : Nat.card (External G h.val) = 6 := by
    simpa only [← Nat.card_coe_set_eq] using le_antisymm
      (show (External G h.val).ncard ≤ 6 from hext)
      (show 6 ≤ (External G h.val).ncard from hc ▸ hcard)
  have heqsets : External G h.val ∩ Covered M = External G h.val :=
    Set.eq_of_subset_of_ncard_le hsub (by
      change Nat.card (External G h.val) ≤ Nat.card ↥(External G h.val ∩ Covered M)
      rw [hext', hc])
  exact ⟨h.property, hr, hext', fun v hv => (heqsets.symm ▸ hv).2⟩

/-- Simultaneous local choices around distance-eight defects form the required seed. -/
theorem separated_dominating_seed {V : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 11)
    (D M : Set G.edgeSet) (hs : Separated G 8 D) (hm : IsMatching M)
    (hdisj : Disjoint D M) :
    ∃ J : Set M, Independent (ConflictGraph G M) J ∧
      (∀ j ∈ J, ∀ r ∈ D, ¬ (L2 G).Adj j.val r) ∧
      ∀ h : M, (∃ r ∈ D, (L2 G).Adj h.val r) →
        Nat.card ((ConflictGraph G M).neighborSet h) = 6 →
        ∃ j ∈ J, (ConflictGraph G M).Adj h j := by
  have hl (r : D) := local_dominators V G hd hg M hm r.val
    (fun hr => Set.disjoint_left.mp hdisj r.property hr)
  choose d hdlocal hdsep using hl
  let I := Σ r : D, {h // ProblemAt G M r.val h}
  let pick : I → M := fun x => d x.1 x.2
  have hwithin (x : I) : WithinFrom G 3 (pick x).val x.1.val := by
    obtain ⟨p,t,he,hp,ht⟩ := (hdlocal x.1 x.2).2
    exact layers_within he hp ht
  have hroot (x : I) : ¬ (L2 G).Adj (pick x).val x.1.val := by
    obtain ⟨p,t,he,hp,ht⟩ := (hdlocal x.1 x.2).2
    exact layers_avoid_root he hp ht
  refine ⟨Set.range pick, ?_, ?_, ?_⟩
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hxy
    by_cases hr : x.1 = y.1
    · rcases x with ⟨r,h⟩
      rcases y with ⟨r',h'⟩
      dsimp at hr
      subst r'
      by_cases hh : h = h'
      · subst h'
        exact (L2 G).irrefl hxy
      · exact hdsep r h h' hh ((conflict_edgeWithin hxy).mono (by decide))
    · exact hs x.1.val x.1.property y.1.val y.1.property
        (fun h => hr (Subtype.ext h)) (within_conflict_within (hwithin x) (hwithin y) hxy)
  · rintro _ ⟨x,rfl⟩ r hr hadj
    by_cases heq : x.1.val = r
    · exact hroot x (heq ▸ hadj)
    · have hself : WithinFrom G 0 r r := fun v hv => ⟨v,hv,.nil,by simp⟩
      exact hs x.1.val x.1.property r hr heq
        ((within_conflict_within (hwithin x) hself hadj).mono (by decide))
  · intro h hnear hdeg
    obtain ⟨r,hr,hconf⟩ := hnear
    let ph : {h // ProblemAt G M r h} :=
      ⟨h.val, degree_six_problem hd (hg.mono (by decide)) hm h hconf hdeg⟩
    exact ⟨d ⟨r,hr⟩ ph, ⟨⟨⟨r,hr⟩, ph⟩, rfl⟩, (hdlocal ⟨r,hr⟩ ph).1⟩

/-- Theorem 3.5 (Theorem B), with exactly the two named literature hypotheses. -/
theorem theorem_B (kost : Kostochka) (hax : Haxell) {V : Type} [Fintype V]
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 39360) :
    StrongColourable G 20 := by
  obtain ⟨D,M,hs,hm,hcover,hdisj⟩ := sparse_four_matching_cover hax hd hg
  obtain ⟨J,hJ,havoid,hdom⟩ := separated_dominating_seed hd (hg.mono (by decide))
    D (M 3) hs (hm 3) (hdisj 3)
  exact twenty_of_dominating_seed kost hd (hg.mono (by decide)) M D hm
    (hs.inducedMatching (by decide)) hcover J hJ havoid hdom

theorem theorem_B_statement : TheoremBStatement := by
  intro kost hax V _ G hd hg
  exact theorem_B kost hax G hd hg

end Se20Part
