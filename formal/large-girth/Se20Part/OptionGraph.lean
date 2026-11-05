import Se20Part.Pseudoforest
import Se20Part.TaggedSelection

noncomputable section
open scoped Classical
open SimpleGraph Finset
namespace Se20Part

/-- An oriented option edge, retaining the defect to which its branch belongs.
The matching edge covering the option is included as a witness. -/
def OptionArcAt {V : Type*} (G : SimpleGraph V) (M : Set G.edgeSet)
    (r : G.edgeSet) (a p : V) : Prop :=
  ∃ h, ProblemAt G M r h ∧ ∃ d ∈ M, ∃ A : DefectArm G r d,
    A.a = a ∧ A.p = p ∧ A.a ∈ h.val ∧ (L2 G).Adj h d

theorem OptionArcAt.adj {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    {r : G.edgeSet} {a p : V} (h : OptionArcAt G M r a p) : G.Adj a p := by
  obtain ⟨_,_,_,_,A,rfl,rfl,_,_⟩ := h
  exact A.ap

/-- The interior of a shortest defect-to-defect path of length 5, 6 or 7,
whose two end edges are options facing along that path. -/
structure FacingCore {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) where
  r : G.edgeSet
  r' : G.edgeSet
  hr : r ∈ D
  hr' : r' ∈ D
  distinct : r ≠ r'
  w : V
  w' : V
  hw : w ∈ r.val
  hw' : w' ∈ r'.val
  a : V
  a' : V
  core : G.Walk a a'
  first : G.Adj w a
  last : G.Adj a' w'
  isPath : core.IsPath
  lower : 3 ≤ core.length
  upper : core.length ≤ 5
  minimal : ∀ x ∈ r.val, ∀ y ∈ r'.val,
    (core.length + 2 : ℕ) ≤ G.edist x y
  firstOption : OptionArcAt G M r a core.snd
  lastOption : OptionArcAt G M r' a' core.penultimate

/-- The manuscript's option graph: all option edges and all facing interiors. -/
def optionGraph {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) : SimpleGraph V where
  Adj x y := G.Adj x y ∧
    ((∃ r ∈ D, OptionArcAt G M r x y) ∨
     (∃ r ∈ D, OptionArcAt G M r y x) ∨
     ∃ P : FacingCore G D M, s(x,y) ∈ P.core.edges)
  symm := ⟨by
    rintro x y ⟨h,ha | ha | ⟨P,hP⟩⟩
    · exact ⟨h.symm,Or.inr (Or.inl ha)⟩
    · exact ⟨h.symm,Or.inl ha⟩
    · exact ⟨h.symm,Or.inr (Or.inr ⟨P,by simpa only [Sym2.eq_swap] using hP⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem optionGraph_option {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    {r : G.edgeSet} (hr : r ∈ D) {a p : V} (h : OptionArcAt G M r a p) :
    (optionGraph G D M).Adj a p := ⟨h.adj,Or.inl ⟨r,hr,h⟩⟩

theorem optionGraph_core {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) {x y : V} (he : s(x,y) ∈ P.core.edges) :
    (optionGraph G D M).Adj x y :=
  ⟨by simpa using P.core.edges_subset_edgeSet he,Or.inr (Or.inr ⟨P,he⟩)⟩

theorem facing_parent_impossible {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) (parent : V → Option V)
    (hc : ∀ u v, (optionGraph G D M).Adj u v →
      parent u = some v ∨ parent v = some u)
    (hf : parent P.core.snd = some P.a)
    (hl : parent P.core.penultimate = some P.a') : False := by
  apply no_facing_parent_choices parent P.core.getVert (by have := P.lower; omega)
    P.isPath.getVert_injOn
  · intro i hi
    apply hc
    apply optionGraph_core P
    exact (P.core.adj_toSubgraph_iff_mem_edges).mp (P.core.toSubgraph_adj_getVert hi)
  · simpa only [Walk.getVert_zero] using hf
  · simpa only [Walk.getVert_length] using hl

theorem problem_arm_avoiding_parent {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (parent : V → Option V)
    {M : Set G.edgeSet} (hm : IsMatching M)
    {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    ∃ d : M, ∃ A : DefectArm G r d.val,
      A.a ∈ h.val ∧ (L2 G).Adj h d.val ∧ parent A.a ≠ some A.p := by
  obtain ⟨w,z,a,hrz,hah,hwa,haz⟩ := problem_branch hr hh
  obtain ⟨b,hhab⟩ := Sym2.mem_iff_exists.mp hah
  have hdeg := external_six_endpoint_degree hd hh.2.2.1 hah
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
    rw [G.card_neighborFinset_eq_degree,hdeg]
    omega
  have hap : G.Adj a p := by simpa using hp
  have hpw : p ≠ w := by intro heq; apply hpn; simp [forbidden,heq]
  have hpb : p ≠ b := by intro heq; apply hpn; simp [forbidden,heq]
  have hnpar : parent a ≠ some p := by intro heq; apply hpn; simp [forbidden,heq]
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
    (matching_conflict_iff hm hh.1 hdm).mpr ⟨p,hpe,hpd⟩,hnpar⟩

/-- The extended local path has length at most nine. Its being geodesic
certifies that the middle path realizes the minimum endpoint distance. -/
theorem core_endpoint_minimal {V : Type*} {G : SimpleGraph V} {r r' d d' : G.edgeSet}
    (hg : GirthAtLeast G 20) (A : DefectArm G r d) (B : DefectArm G r' d')
    (q : G.Walk A.a B.a) (hupper : q.length ≤ 5)
    (hn : NoBacktrack (.cons A.root_adj.symm (.cons A.wa
      ((q.concat B.wa.symm).concat B.root_adj)))) :
    q.IsPath ∧ ∀ x ∈ r.val, ∀ y ∈ r'.val, (q.length+2 : ℕ) ≤ G.edist x y := by
  let p := Walk.cons A.root_adj.symm (Walk.cons A.wa
    ((q.concat B.wa.symm).concat B.root_adj))
  have hl : 2*p.length < 20 := by simp only [p,Walk.length_cons,Walk.length_concat]; omega
  have hp := short_noBacktrack_isPath hg p hn (by omega)
  have hpq : q.IsPath := by
    have hh := hp.of_cons.of_cons
    exact ((Walk.isPath_concat B.wa.symm).mp ((Walk.isPath_concat B.root_adj).mp hh).1).1
  refine ⟨hpq,?_⟩
  intro x hx y hy
  have hdist := short_noBacktrack_edist hg p hn hl
  have hzx : G.edist A.z x ≤ 1 := by
    obtain ⟨w,hw,_⟩ := walk_inside_edge r (x := A.z) (y := x) (by simp [A.root]) hx
    exact w.edist_le.trans (by exact_mod_cast hw)
  have hyz : G.edist y B.z ≤ 1 := by
    obtain ⟨w,hw,_⟩ := walk_inside_edge r' (x := y) (y := B.z) hy (by simp [B.root])
    exact w.edist_le.trans (by exact_mod_cast hw)
  have hh : (p.length : ℕ∞) ≤ 1 + G.edist x y + 1 := by
    rw [← hdist]
    have ht₁ := G.edist_triangle (u := A.z) (v := x) (w := B.z)
    have ht₂ := G.edist_triangle (u := x) (v := y) (w := B.z)
    simpa only [add_assoc] using ht₁.trans
      (add_le_add hzx (ht₂.trans (add_le_add le_rfl hyz)))
  have hlen : p.length = q.length + 4 := by simp only [p,Walk.length_cons,Walk.length_concat]
  rw [hlen,Nat.cast_add] at hh
  have hh' : (q.length+2 : ℕ∞) + 2 ≤ G.edist x y + 2 := by
    convert hh using 1 <;> norm_num <;> ring
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'

theorem arms_conflict_facing {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (hg : GirthAtLeast G 20) (hm : IsMatching M)
    {r r' h h' d d' : G.edgeSet} (hr : r ∈ D) (hr' : r' ∈ D) (hrr : r ≠ r')
    (hprob : ProblemAt G M r h) (hprob' : ProblemAt G M r' h')
    (hd : d ∈ M) (hd' : d' ∈ M)
    (A : DefectArm G r d) (B : DefectArm G r' d')
    (ha : A.a ∈ h.val) (hb : B.a ∈ h'.val)
    (ho : OptionArcAt G M r A.a A.p) (ho' : OptionArcAt G M r' B.a B.p)
    (hsafe : ¬ (L2 G).Adj d r') (hsafe' : ¬ (L2 G).Adj d' r)
    (hconf : (L2 G).Adj d d') :
    ∃ P : FacingCore G D M, P.a = A.a ∧ P.a' = B.a ∧
      P.core.snd = A.p ∧ P.core.penultimate = B.p := by
  have hcross {x y : V} (hx : x ∈ d.val) (hy : y ∈ d'.val) : x ≠ y := by
    intro heq
    exact hconf.1 (hm hd hd' hx (heq ▸ hy))
  have hna {y : V} (hy : y ∈ d'.val) : A.a ≠ y := by
    intro heq
    have he := hm hprob.1 hd' ha (heq ▸ hy)
    apply hsafe'
    rw [← he]
    exact hprob.2.1
  have hnb {x : V} (hx : x ∈ d.val) : x ≠ B.a := by
    intro heq
    have he := hm hd hprob'.1 hx (heq ▸ hb)
    apply hsafe
    rw [he]
    exact hprob'.2.1
  have hpp : A.p ≠ B.p := hcross (by simp [A.edge]) (by simp [B.edge])
  have hpt : A.p ≠ B.t := hcross (by simp [A.edge]) (by simp [B.edge])
  have htp : A.t ≠ B.p := hcross (by simp [A.edge]) (by simp [B.edge])
  have htt : A.t ≠ B.t := hcross (by simp [A.edge]) (by simp [B.edge])
  have hap : A.a ≠ B.p := hna (by simp [B.edge])
  have hat : A.a ≠ B.t := hna (by simp [B.edge])
  have hpa : A.p ≠ B.a := hnb (by simp [A.edge])
  have hta : A.t ≠ B.a := hnb (by simp [A.edge])
  have make (q : G.Walk A.a B.a) (hlo : 3 ≤ q.length) (hhi : q.length ≤ 5)
      (hsnd : q.snd = A.p) (hpen : q.penultimate = B.p)
      (hn : NoBacktrack (.cons A.root_adj.symm (.cons A.wa
        ((q.concat B.wa.symm).concat B.root_adj)))) :
      ∃ P : FacingCore G D M, P.a = A.a ∧ P.a' = B.a ∧
        P.core.snd = A.p ∧ P.core.penultimate = B.p := by
    have hh := core_endpoint_minimal hg A B q hhi hn
    let P : FacingCore G D M := {
      r := r, r' := r', hr := hr, hr' := hr', distinct := hrr
      w := A.w, w' := B.w, hw := by simp [A.root], hw' := by simp [B.root]
      a := A.a, a' := B.a, core := q, first := A.wa, last := B.wa.symm
      isPath := hh.1, lower := hlo, upper := hhi, minimal := hh.2
      firstOption := hsnd ▸ ho, lastOption := hpen ▸ ho' }
    exact ⟨P,rfl,rfl,hsnd,hpen⟩
  obtain ⟨_,x,hx,y,hy,hxy⟩ := hconf
  have hadj : G.Adj x y := hxy.resolve_left (hcross hx hy)
  rw [A.edge,Sym2.mem_iff] at hx
  rw [B.edge,Sym2.mem_iff] at hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · apply make (.cons A.ap (.cons hadj (.cons B.ap.symm .nil)))
      (by simp) (by simp) rfl rfl
    simp [NoBacktrack,Walk.concat,A.az.symm,A.pw.symm,hap,hpa,B.pw,B.az]
  · apply make (.cons A.ap (.cons hadj (.cons B.pt.symm (.cons B.ap.symm .nil))))
      (by simp) (by simp) rfl rfl
    simp [NoBacktrack,Walk.concat,A.az.symm,A.pw.symm,hat,hpp,B.ta,B.pw,B.az]
  · apply make (.cons A.ap (.cons A.pt (.cons hadj (.cons B.ap.symm .nil))))
      (by simp) (by simp) rfl rfl
    simp [NoBacktrack,Walk.concat,A.az.symm,A.pw.symm,A.ta.symm,hpp,hta,B.pw,B.az]
  · apply make (.cons A.ap (.cons A.pt (.cons hadj (.cons B.pt.symm (.cons B.ap.symm .nil)))))
      (by simp) (by simp) rfl rfl
    simp [NoBacktrack,Walk.concat,A.az.symm,A.pw.symm,A.ta.symm,hpt,htp,B.ta,B.pw,B.az]

/-- The finite coordination step: a parent map on the constructed option graph
gives a seed for distance-five defects. -/
theorem option_parent_seed {V : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 20)
    (D M : Set G.edgeSet) (hs : Separated G 5 D) (hm : IsMatching M)
    (hdisj : Disjoint D M) (parent : V → Option V)
    (hc : ∀ u v, (optionGraph G D M).Adj u v →
      parent u = some v ∨ parent v = some u) :
    ∃ J : Set M, Independent (ConflictGraph G M) J ∧
      (∀ j ∈ J, ∀ r ∈ D, ¬ (L2 G).Adj j.val r) ∧
      ∀ h : M, (∃ r ∈ D, (L2 G).Adj h.val r) →
        Nat.card ((ConflictGraph G M).neighborSet h) = 6 →
        ∃ j ∈ J, (ConflictGraph G M).Adj h j := by
  have hchoice (r : D) (h : {h // ProblemAt G M r.val h}) :=
    problem_arm_avoiding_parent hd parent hm
      (fun hr => Set.disjoint_left.mp hdisj r.property hr) h.property
  choose d A ha hadj hnpar using hchoice
  let I := Σ r : D, {h // ProblemAt G M r.val h}
  let pick : I → M := fun x => d x.1 x.2
  have hopt (x : I) : OptionArcAt G M x.1.val (A x.1 x.2).a (A x.1 x.2).p :=
    ⟨x.2.val,x.2.property,(d x.1 x.2).val,(d x.1 x.2).property,A x.1 x.2,
      rfl,rfl,ha x.1 x.2,hadj x.1 x.2⟩
  have hpar (x : I) : parent (A x.1 x.2).p = some (A x.1 x.2).a :=
    (hc _ _ (optionGraph_option x.1.property (hopt x))).resolve_left (hnpar x.1 x.2)
  have havoid (x : I) (r : G.edgeSet) (hr : r ∈ D) : ¬ (L2 G).Adj (pick x).val r := by
    have hl := (A x.1 x.2).layers (hg.mono (by decide))
    by_cases heq : x.1.val = r
    · exact heq ▸ layers_avoid_root (A x.1 x.2).edge hl.1 hl.2
    · intro hadj
      have hself : WithinFrom G 0 r r := fun v hv => ⟨v,hv,.nil,by simp⟩
      exact hs x.1.val x.1.property r hr heq
        (within_conflict_within (layers_within (A x.1 x.2).edge hl.1 hl.2) hself hadj)
  refine ⟨Set.range pick,?_,?_,?_⟩
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hconf
    by_cases hrr : x.1.val = y.1.val
    · have hrsub : x.1 = y.1 := Subtype.ext hrr
      rcases x with ⟨r,h⟩
      rcases y with ⟨r',h'⟩
      dsimp at hrsub
      subst r'
      by_cases hh : h = h'
      · subst h'; exact (L2 G).irrefl hconf
      · have hbranches : (A r h).a ≠ (A r h').a := by
          intro heq
          exact hh (Subtype.ext (hm h.property.1 h'.property.1 (ha r h) (heq ▸ ha r h')))
        exact DefectArm.separated (hg.mono (by decide)) (A r h) (A r h') hbranches
          ((conflict_edgeWithin hconf).mono (by decide))
    · obtain ⟨P,hstart,hend,hsnd,hpen⟩ := arms_conflict_facing hg hm
        x.1.property y.1.property hrr x.2.property y.2.property
        (d x.1 x.2).property (d y.1 y.2).property (A x.1 x.2) (A y.1 y.2)
        (ha x.1 x.2) (ha y.1 y.2) (hopt x) (hopt y)
        (havoid x _ y.1.property) (havoid y _ x.1.property) hconf
      exact facing_parent_impossible P parent hc
        (by simpa only [hsnd,hstart] using hpar x)
        (by simpa only [hpen,hend] using hpar y)
  · rintro j ⟨x,rfl⟩ r hr; exact havoid x r hr
  · intro h hnear hdeg
    obtain ⟨r,hr,hconf⟩ := hnear
    let ph : {h // ProblemAt G M r h} :=
      ⟨h.val,degree_six_problem hd (hg.mono (by decide)) hm h hconf hdeg⟩
    exact ⟨d ⟨r,hr⟩ ph,⟨⟨⟨r,hr⟩,ph⟩,rfl⟩,hadj ⟨r,hr⟩ ph⟩

/-- Proposition 3.13. The supplied matching cover may be the one constructed
by Haxell at 1452; only the constructed option graph is assumed pseudoforest. -/
theorem proposition_3_13 {V : Type} [Fintype V] (kost : Kostochka)
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 1452)
    (D : Set G.edgeSet) (M : Fin 4 → Set G.edgeSet)
    (hs : Separated G 5 D) (hm : ∀ i, IsMatching (M i))
    (hcover : ∀ e, e ∈ D ∨ ∃ i, e ∈ M i) (hdisj : Disjoint D (M 3))
    (hU : IsPseudoforest (optionGraph G D (M 3))) : StrongColourable G 20 := by
  obtain ⟨parent,hparent⟩ := pseudoforest_parent hU
  obtain ⟨J,hJ,havoid,hdom⟩ := option_parent_seed hd (hg.mono (by decide)) D (M 3)
    hs (hm 3) hdisj parent hparent
  exact twenty_of_dominating_seed kost hd (hg.mono (by decide)) M D hm
    (hs.inducedMatching (by decide)) hcover J hJ havoid hdom

end Se20Part
