import Se20Part.DeadEdges

noncomputable section
open scoped Classical
open SimpleGraph Finset
namespace Se20Part

/-- A rooted tree admits a parent map covering every edge, without any finiteness assumption. -/
theorem tree_parent {V : Type*} {G : SimpleGraph V} (ht : G.IsTree) :
    ∃ parent : V → Option V, ∀ u v, G.Adj u v →
      parent u = some v ∨ parent v = some u := by
  letI : Nonempty V := ht.connected.nonempty
  let root : V := Classical.choice (inferInstance : Nonempty V)
  choose p hp _ using fun v => ht.connected.exists_path_of_dist v root
  let parent : V → Option V := fun v => if v = root then none else some (p v).snd
  refine ⟨parent, fun u v huv => ?_⟩
  by_cases hv : v ∈ (p u).support
  · have hu : u ≠ root := by
      intro hur
      have hn := (hp u).nil_iff_eq.mpr hur
      have hvu : v = u := by simpa only [Walk.nil_iff_support_eq.mp hn, List.mem_singleton] using hv
      exact huv.ne hvu.symm
    exact Or.inl (by simp [parent,hu,ht.isAcyclic.eq_snd_of_adj_start (hp u) huv hv])
  · have hvroot : v ≠ root := fun h => hv (h ▸ (p u).end_mem_support)
    have hpath : (Walk.cons huv.symm (p u)).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp u,hv⟩
    have heq : Walk.cons huv.symm (p u) = p v := congrArg Subtype.val
      ((ht.isAcyclic.subsingleton_path v root).elim ⟨_,hpath⟩ ⟨_,hp v⟩)
    exact Or.inr (by simp [parent,hvroot,← heq])

theorem problem_branch_general {V : Type*} {G : SimpleGraph V}
    {M : Set G.edgeSet} {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    ∃ w z a, r.val = s(w,z) ∧ a ∈ h.val ∧ G.Adj w a ∧ a ≠ z := by
  have hne : h ≠ r := fun h => hr (h ▸ hh.1)
  by_cases hmeet : ∃ w, w ∈ r.val ∧ w ∈ h.val
  · obtain ⟨w,hwr,hwh⟩ := hmeet
    obtain ⟨z,hrz⟩ := Sym2.mem_iff_exists.mp hwr
    obtain ⟨a,hha⟩ := Sym2.mem_iff_exists.mp hwh
    have hwa : G.Adj w a := by simpa [hha] using h.property
    refine ⟨w,z,a,hrz,by simp [hha],hwa,?_⟩
    intro haz
    exact hne (Subtype.ext (by rw [hha,hrz,haz]))
  · obtain ⟨_,a,hah,w,hwr,haw⟩ := hh.2.1
    have hawn : a ≠ w := fun haw => hmeet ⟨w,hwr,haw ▸ hah⟩
    have hwa : G.Adj w a := (haw.resolve_left hawn).symm
    obtain ⟨z,hrz⟩ := Sym2.mem_iff_exists.mp hwr
    refine ⟨w,z,a,hrz,hah,hwa,?_⟩
    intro haz
    exact hmeet ⟨a,by simp [hrz,haz],hah⟩

theorem problem_arm_parent {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (hd : ∀ v, G.degree v = 4) (parent : V → Option V)
    (hc : ∀ u v, G.Adj u v → parent u = some v ∨ parent v = some u)
    {M : Set G.edgeSet} (hm : IsMatching M)
    {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    ∃ d : M, ∃ A : DefectArm G r d.val,
      A.a ∈ h.val ∧ (L2 G).Adj h d.val ∧ parent A.p = some A.a := by
  obtain ⟨w,z,a,hrz,hah,hwa,haz⟩ := problem_branch_general hr hh
  obtain ⟨b,hhab⟩ := Sym2.mem_iff_exists.mp hah
  let forbidden : Finset V := {w,b} ∪ (parent a).toFinset
  have hsmall : forbidden.card ≤ 3 := by
    cases hpa : parent a with
    | none =>
      have := Finset.card_insert_le w ({b} : Finset V)
      simpa [forbidden,hpa] using this.trans (by simp : ({b} : Finset V).card+1 ≤ 3)
    | some v =>
      have h₁ := Finset.card_union_le ({w,b} : Finset V) ({v} : Finset V)
      have h₂ := Finset.card_insert_le w ({b} : Finset V)
      simp only [Finset.card_singleton] at h₁ h₂
      simpa [forbidden,hpa] using (show ({w,b} ∪ {v} : Finset V).card ≤ 3 by omega)
  obtain ⟨p,hp,hpn⟩ : ∃ p ∈ G.neighborFinset a, p ∉ forbidden := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [G.card_neighborFinset_eq_degree,hd]
    omega
  have hap : G.Adj a p := by simpa using hp
  have hpw : p ≠ w := by intro heq; apply hpn; simp [forbidden,heq]
  have hpb : p ≠ b := by intro heq; apply hpn; simp [forbidden,heq]
  have hnpar : parent a ≠ some p := by intro heq; apply hpn; simp [forbidden,heq]
  have hpar : parent p = some a := (hc a p hap).resolve_left hnpar
  have hpe : p ∈ External G h := by
    refine ⟨?_,a,hah,hap⟩
    simpa [hhab,Sym2.mem_iff] using And.intro hap.ne.symm hpb
  obtain ⟨d,hdm,hpd⟩ := hh.2.2.2 hpe
  obtain ⟨t,hdt⟩ := Sym2.mem_iff_exists.mp hpd
  have hpt : G.Adj p t := by simpa [hdt] using d.property
  have hdh : d ≠ h := fun heq => hpe.1 (heq ▸ hpd)
  have hta : t ≠ a := by
    intro hta
    exact hdh (hm hdm hh.1 (v := a) (by simp [hdt,hta]) hah)
  exact ⟨⟨d,hdm⟩,⟨w,z,a,p,t,hrz,hdt,hwa,hap,hpt,haz,hpw,hta⟩,hah,
    (matching_conflict_iff hm hh.1 hdm).mpr ⟨p,hpe,hpd⟩,hpar⟩

/-- Parent choices can conflict only when one chosen dominator is the other
problem edge. This avoids a separate facing-path induction in the tree case. -/
theorem parent_choices_conflict {V : Type*} {G : SimpleGraph V}
    (parent : V → Option V)
    (hc : ∀ u v, G.Adj u v → parent u = some v ∨ parent v = some u)
    {M : Set G.edgeSet} (hm : IsMatching M)
    {h h' d d' r r' : G.edgeSet} (hh : h ∈ M) (hh' : h' ∈ M)
    (hd : d ∈ M) (hd' : d' ∈ M)
    (A : DefectArm G r d) (B : DefectArm G r' d')
    (ha : A.a ∈ h.val) (hb : B.a ∈ h'.val)
    (hpa : parent A.p = some A.a) (hpb : parent B.p = some B.a)
    (hconf : (L2 G).Adj d d') : h = d' ∨ h' = d := by
  have hta : parent A.t = some A.p := (hc A.p A.t A.pt).resolve_left
    (fun h => A.ta (Option.some.inj (h.symm.trans hpa)))
  have htb : parent B.t = some B.p := (hc B.p B.t B.pt).resolve_left
    (fun h => B.ta (Option.some.inj (h.symm.trans hpb)))
  have upstream {r d h d' : G.edgeSet} (A : DefectArm G r d)
      (hd : d ∈ M) (hh : h ∈ M) (hd' : d' ∈ M) (ha : A.a ∈ h.val)
      (hpa : parent A.p = some A.a) (hta : parent A.t = some A.p)
      {x y : V} (hx : x ∈ d.val) (hy : y ∈ d'.val) (hpar : parent x = some y) :
      h = d' ∨ d = d' := by
    rw [A.edge,Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · have heq : A.a = y := Option.some.inj (hpa.symm.trans hpar)
      exact Or.inl (hm hh hd' ha (heq ▸ hy))
    · have heq : A.p = y := Option.some.inj (hta.symm.trans hpar)
      exact Or.inr (hm hd hd' (by simp [A.edge]) (heq ▸ hy))
  obtain ⟨hne,x,hx,y,hy,hxy⟩ := hconf
  rcases hxy with heq | hxy
  · exact (hne (hm hd hd' hx (heq ▸ hy))).elim
  · rcases hc x y hxy with hpar | hpar
    · exact Or.inl ((upstream A hd hh hd' ha hpa hta hx hy hpar).resolve_right hne)
    · exact Or.inr ((upstream B hd' hh' hd hb hpb htb hy hx hpar).resolve_right hne.symm)

/-- A stronger tree form: the two-factor and nondefect-coverage assumptions are
not needed once a problem edge is defined to have all external vertices covered. -/
theorem infinite_tree_seed (T : InfiniteFourTree) (D M : Set T.graph.edgeSet)
    (hs : Separated T.graph 5 D) (hm : IsMatching M) (hdisj : Disjoint D M) :
    ∃ J : Set T.graph.edgeSet, J ⊆ M ∧ IsInducedMatching J ∧
      (∀ e ∈ J, ∀ r ∈ D, ¬ (L2 T.graph).Adj e r) ∧
      ∀ h, Problem T.graph D M h → ∃ d ∈ J, (L2 T.graph).Adj h d := by
  letI : T.graph.LocallyFinite := fun v => (T.finite_neighbors v).fintype
  have hd (v : T.Vertex) : T.graph.degree v = 4 := by
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using T.degree_four v
  have hg : GirthAtLeast T.graph 11 := fun _ p hp => (T.isTree.isAcyclic p hp).elim
  obtain ⟨parent,hparent⟩ := tree_parent T.isTree
  have hchoice (r : D) (h : {h // ProblemAt T.graph M r.val h}) :=
    problem_arm_parent hd parent hparent hm
      (fun hr => Set.disjoint_left.mp hdisj r.property hr) h.property
  choose d A ha hadj hpar using hchoice
  let I := Σ r : D, {h // ProblemAt T.graph M r.val h}
  let pick : I → T.graph.edgeSet := fun x => (d x.1 x.2).val
  have havoid (x : I) (r : T.graph.edgeSet) (hr : r ∈ D) : ¬ (L2 T.graph).Adj (pick x) r := by
    have hl := (A x.1 x.2).layers hg
    by_cases heq : x.1.val = r
    · exact heq ▸ layers_avoid_root (A x.1 x.2).edge hl.1 hl.2
    · intro hc
      have hself : WithinFrom T.graph 0 r r := fun v hv => ⟨v,hv,.nil,by simp⟩
      exact hs x.1.val x.1.property r hr heq
        (within_conflict_within (layers_within (A x.1 x.2).edge hl.1 hl.2) hself hc)
  refine ⟨Set.range pick, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨x,rfl⟩
    exact (d x.1 x.2).property
  · rintro e ⟨x,rfl⟩ f ⟨y,rfl⟩ hconf
    have hp := parent_choices_conflict parent hparent hm x.2.property.1 y.2.property.1
      (d x.1 x.2).property (d y.1 y.2).property (A x.1 x.2) (A y.1 y.2)
      (ha x.1 x.2) (ha y.1 y.2) (hpar x.1 x.2) (hpar y.1 y.2) hconf
    rcases hp with hp | hp
    · apply havoid y x.1.val x.1.property
      change (L2 T.graph).Adj (d y.1 y.2).val x.1.val
      rw [← hp]
      exact x.2.property.2.1
    · apply havoid x y.1.val y.1.property
      change (L2 T.graph).Adj (d x.1 x.2).val y.1.val
      rw [← hp]
      exact y.2.property.2.1
  · rintro e ⟨x,rfl⟩ r hr
    exact havoid x r hr
  · rintro h ⟨r,hr,hprob⟩
    exact ⟨(d ⟨r,hr⟩ ⟨h,hprob⟩).val,⟨⟨⟨r,hr⟩,⟨h,hprob⟩⟩,rfl⟩,hadj ⟨r,hr⟩ ⟨h,hprob⟩⟩

theorem tree_lemma : TreeLemmaStatement := by
  intro T F₁ F₂ D M _ _ _ _ hs hm hM _
  apply infinite_tree_seed T D M hs hm
  exact Set.disjoint_left.mpr (fun e he hm => (hM hm).2 he)

end Se20Part
