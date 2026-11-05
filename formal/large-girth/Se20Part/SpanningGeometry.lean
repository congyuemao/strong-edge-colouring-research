import Se20Part.OptionGraph

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

theorem optionGraph_le {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) :
    optionGraph G D M ≤ G := fun _ _ h => h.1

theorem OptionArcAt.avoids_defects {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {r : G.edgeSet} (hr : r ∈ D) {a p : V} (ho : OptionArcAt G M r a p) :
    a ∉ Covered D ∧ p ∉ Covered D := by
  obtain ⟨_,_,_,_,A,rfl,rfl,_,_⟩ := ho
  have ha : A.a ∉ r.val := by
    simpa [A.root,Sym2.mem_iff] using And.intro A.wa.ne.symm A.az
  have hp : A.p ∉ r.val := by
    intro hh
    have := (A.layers hg).1.1 A.p hh
    simpa using this
  constructor
  · rintro ⟨r',hr',har'⟩
    by_cases heq : r = r'
    · exact ha (heq ▸ har')
    · exact hs r hr r' hr' heq ⟨A.w,by simp [A.root],A.a,har',
        .cons A.wa .nil,by simp⟩
  · rintro ⟨r',hr',hpr'⟩
    by_cases heq : r = r'
    · exact hp (heq ▸ hpr')
    · exact hs r hr r' hr' heq ⟨A.w,by simp [A.root],A.p,hpr',
        .cons A.wa (.cons A.ap .nil),by simp⟩

theorem FacingCore.avoids_defects {V : Type*} {G : SimpleGraph V}
    {D M : Set G.edgeSet} (hs : Separated G 5 D) (P : FacingCore G D M)
    {v : V} (hv : v ∈ P.core.support) : v ∉ Covered D := by
  obtain ⟨i,rfl,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  let left : G.Walk P.w (P.core.getVert i) := .cons P.first (P.core.take i)
  let right : G.Walk (P.core.getVert i) P.w' := (P.core.drop i).concat P.last
  have hl : left.length = i+1 := by simp [left,Walk.take_length,Nat.min_eq_left hi]
  have hr : right.length = P.core.length-i+1 := by simp [right]
  rintro ⟨r,hrD,hvr⟩
  by_cases heq : r = P.r
  · have h := (P.minimal _ (heq ▸ hvr) _ P.hw').trans right.edist_le
    rw [hr] at h
    have : P.core.length+2 ≤ P.core.length-i+1 := by exact_mod_cast h
    omega
  by_cases heq' : r = P.r'
  · have h := (P.minimal _ P.hw _ (heq' ▸ hvr)).trans left.edist_le
    rw [hl] at h
    have : P.core.length+2 ≤ i+1 := by exact_mod_cast h
    omega
  by_cases hil : i ≤ 2
  · exact hs P.r P.hr r hrD (Ne.symm heq) ⟨P.w,P.hw,_,hvr,left,by rw [hl]; omega⟩
  · exact hs r hrD P.r' P.hr' heq' ⟨_,hvr,P.w',P.hw',right,by
      rw [hr]; have := P.upper; omega⟩

/-- Lemma 3.15, step 2, on every vertex incident with the option graph. -/
theorem optionGraph_avoids_defects {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {x y : V} (he : (optionGraph G D M).Adj x y) :
    x ∉ Covered D ∧ y ∉ Covered D := by
  rcases he.2 with ⟨r,hr,ho⟩ | ⟨r,hr,ho⟩ | ⟨P,hP⟩
  · exact ho.avoids_defects hg hs hr
  · exact (ho.avoids_defects hg hs hr).symm
  · exact ⟨P.avoids_defects hs (P.core.mem_support_of_mem_edges hP (by simp)),
      P.avoids_defects hs (P.core.mem_support_of_mem_edges hP (by simp))⟩

/-- A short cycle segment in U is geodesic in the ambient graph. -/
theorem option_cycle_segment_geodesic {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {D M : Set G.edgeSet} {v : V}
    (Z : (optionGraph G D M).Walk v v) (hz : Z.IsCycle) {n : ℕ}
    (hn : 2*n < g) :
    ((Z.take n).mapLe (optionGraph_le G D M)).length =
      G.dist v (Z.getVert n) := by
  have hgZ : g ≤ Z.length := by
    simpa using hg v (Z.mapLe (optionGraph_le G D M)) (hz.mapLe _)
  apply short_path_geodesic hg _ ((hz.isPath_take (by omega)).mapLe _)
  simpa [Walk.take_length,Nat.min_eq_left (show n ≤ Z.length by omega)] using hn

theorem isPath_noBacktrack {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : NoBacktrack p := by
  induction p with
  | nil => trivial
  | @cons u v w h p ih =>
    have hh : p.IsPath ∧ u ∉ p.support := by simpa only [Walk.cons_isPath_iff] using hp
    exact ⟨Or.inr (fun heq => hh.2 (heq ▸ p.getVert_mem_support 1)),ih hh.1⟩

def FacingCore.full {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) : G.Walk P.w P.w' := .cons P.first (P.core.concat P.last)

theorem FacingCore.full_length {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) : P.full.length = P.core.length+2 := by simp [full]

theorem FacingCore.full_isPath {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) : P.full.IsPath := by
  apply P.full.isPath_of_length_eq_dist
  apply le_antisymm
  · have hh := P.minimal _ P.hw _ P.hw'
    rw [← P.full.reachable.coe_dist_eq_edist] at hh
    rw [P.full_length]
    exact_mod_cast hh
  · exact G.dist_le P.full

/-- A cycle edge is certified by a short path between distinct defects. -/
def DefectBridge {V : Type*} (G : SimpleGraph V) (D : Set G.edgeSet) (e : Sym2 V) : Prop :=
  ∃ r ∈ D, ∃ r' ∈ D, r ≠ r' ∧ ∃ w ∈ r.val, ∃ w' ∈ r'.val,
    ∃ q : G.Walk w w', q.IsPath ∧ q.length ≤ 7 ∧ e ∈ q.edges

theorem FacingCore.bridge {V : Type*} {G : SimpleGraph V} {D M : Set G.edgeSet}
    (P : FacingCore G D M) {e : Sym2 V} (he : e ∈ P.core.edges) : DefectBridge G D e := by
  refine ⟨P.r,P.hr,P.r',P.hr',P.distinct,P.w,P.hw,P.w',P.hw',P.full,P.full_isPath,?_,?_⟩
  · rw [P.full_length]; have := P.upper; omega
  · simp [full,he]

theorem OptionArcAt.no_option_turn {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {r : G.edgeSet} (hr : r ∈ D) {a p q : V} (ho : OptionArcAt G M r a p)
    (hqa : q ≠ a) :
    ¬ ((∃ r' ∈ D, OptionArcAt G M r' p q) ∨
       (∃ r' ∈ D, OptionArcAt G M r' q p)) := by
  obtain ⟨_,_,d,_,A,rfl,rfl,_,_⟩ := ho
  rintro (⟨r',hr',_,_,d',_,B,hBa,hBp,_,_⟩ | ⟨r',hr',_,_,d',_,B,hBa,hBp,_,_⟩)
  · have heq : r = r' := by
      by_contra hne
      apply hs r hr r' hr' hne
      refine ⟨A.w,by simp [A.root],B.w,by simp [B.root],
        .cons A.wa (.cons A.ap (.cons (hBa ▸ B.wa.symm) .nil)),by simp⟩
    have hmem : B.w ∈ r.val := by rw [heq]; simp [B.root]
    have hh := (A.layers hg).1.1 B.w hmem
    have hle : G.edist A.p B.w ≤ 1 := by simpa [hBa] using B.wa.symm.toWalk.edist_le
    have := hh.trans hle
    norm_num at this
  · have heq : r = r' := by
      by_contra hne
      apply hs r hr r' hr' hne
      refine ⟨A.w,by simp [A.root],B.w,by simp [B.root],
        .cons A.wa (.cons A.ap (.cons (hBp ▸ B.ap.symm) (.cons B.wa.symm .nil))),by simp⟩
    subst r'
    apply A.separated hg B (by simpa [hBa] using hqa.symm)
    exact ⟨A.p,by simp [A.edge],A.p,by simp [B.edge,hBp],.nil,by simp⟩

theorem cycle_other_neighbor {V : Type*} {G : SimpleGraph V} {v a p : V}
    {Z : G.Walk v v} (hz : Z.IsCycle) (he : s(a,p) ∈ Z.edges) :
    ∃ q, q ≠ a ∧ s(p,q) ∈ Z.edges := by
  have hp := Z.snd_mem_support_of_mem_edges he
  have hc := hz.ncard_neighborSet_toSubgraph_eq_two hp
  by_contra! hh
  have hsub : Z.toSubgraph.neighborSet p ⊆ {a} := by
    intro q hq
    by_contra hqa
    exact hh q (by simpa using hqa) ((Z.adj_toSubgraph_iff_mem_edges).mp hq)
  have := Set.ncard_le_ncard hsub
  simp [hc] at this

theorem OptionArcAt.bridge_of_core {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {r : G.edgeSet} (hr : r ∈ D) {a p : V} (ho : OptionArcAt G M r a p)
    (P : FacingCore G D M) (hp : p ∈ P.core.support)
    (hne : s(a,p) ∉ P.core.edges) : DefectBridge G D s(a,p) := by
  have hav := ho.avoids_defects hg hs hr
  have hno : s(a,p) ∉ P.full.edges := by
    simp only [FacingCore.full,Walk.edges_cons,Walk.edges_concat,List.mem_cons,
      List.concat_eq_append,List.mem_append,List.not_mem_nil,or_false]
    rintro (h | h | h)
    · have hh : P.w ∈ s(a,p) := by rw [h]; simp
      rcases Sym2.mem_iff.mp hh with hh | hh
      · exact hav.1 ⟨P.r,P.hr,hh ▸ P.hw⟩
      · exact hav.2 ⟨P.r,P.hr,hh ▸ P.hw⟩
    · exact hne h
    · have hh : P.w' ∈ s(a,p) := by rw [h]; simp
      rcases Sym2.mem_iff.mp hh with hh | hh
      · exact hav.1 ⟨P.r',P.hr',hh ▸ P.hw'⟩
      · exact hav.2 ⟨P.r',P.hr',hh ▸ P.hw'⟩
  have hpf : p ∈ P.full.support := by simp [FacingCore.full,hp]
  have hlen : (P.full.takeUntil p hpf).length + (P.full.dropUntil p hpf).length ≤ 7 := by
    rw [← Walk.length_append,P.full.take_spec hpf,P.full_length]
    have := P.upper; omega
  obtain ⟨r',hr',w',hw',q,hq,hql,hqe⟩ :
      ∃ r' ∈ D, ∃ w' ∈ r'.val, ∃ q : G.Walk p w',
        q.IsPath ∧ q.length ≤ 3 ∧ s(a,p) ∉ q.edges := by
    by_cases hl : (P.full.takeUntil p hpf).length ≤ 3
    · refine ⟨P.r,P.hr,P.w,P.hw,(P.full.takeUntil p hpf).reverse,
        (P.full_isPath.takeUntil hpf).reverse,by simpa using hl,?_⟩
      intro hh
      apply hno
      have he : s(a,p) ∈ (P.full.takeUntil p hpf).edges := by simpa using hh
      rw [← P.full.take_spec hpf,Walk.edges_append]
      exact List.mem_append_left _ he
    · refine ⟨P.r',P.hr',P.w',P.hw',P.full.dropUntil p hpf,
        P.full_isPath.dropUntil hpf,by omega,?_⟩
      intro hh
      apply hno
      rw [← P.full.take_spec hpf,Walk.edges_append]
      exact List.mem_append_right _ hh
  obtain ⟨_,_,d,_,A,rfl,rfl,_,_⟩ := ho
  let Q : G.Walk A.w w' := .cons A.wa (.cons A.ap q)
  have hnb : NoBacktrack Q := by
    refine ⟨Or.inr (by simpa using A.pw.symm),?_,isPath_noBacktrack hq⟩
    by_cases hn : q.Nil
    · exact Or.inl hn
    · apply Or.inr
      intro hh
      apply hqe
      simpa only [hh,Sym2.eq_swap] using q.mk_start_snd_mem_edges hn
  have hQl : Q.length = q.length+2 := by simp [Q]
  have hpath := short_noBacktrack_isPath hg Q hnb (by rw [hQl]; omega)
  have hrr : r ≠ r' := by
    intro heq
    have hwr : w' ∈ r.val := by rw [heq]; exact hw'
    obtain ⟨t,ht,_⟩ := walk_inside_edge r (x := A.w) (y := w') (by simp [A.root]) hwr
    have he := short_noBacktrack_edist hg Q hnb (by rw [hQl]; omega)
    have : (Q.length : ℕ∞) ≤ 1 := by
      rw [← he]
      exact t.edist_le.trans (by exact_mod_cast ht)
    have : Q.length ≤ 1 := by exact_mod_cast this
    rw [hQl] at this
    omega
  exact ⟨r,hr,r',hr',hrr,A.w,by simp [A.root],w',hw',Q,hpath,
    by rw [hQl]; omega,by simp [Q]⟩

/-- Lemma 3.15, step 4: every edge of an option-graph cycle lies on a
simple path of length at most seven between two distinct defects. -/
theorem option_cycle_edge_bridge {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {v a p : V} {Z : (optionGraph G D M).Walk v v} (hz : Z.IsCycle)
    (he : s(a,p) ∈ Z.edges) : DefectBridge G D s(a,p) := by
  have hU : (optionGraph G D M).Adj a p := by simpa using Z.edges_subset_edgeSet he
  have hcase {r : G.edgeSet} (hr : r ∈ D) {a p : V}
      (ho : OptionArcAt G M r a p) (he : s(a,p) ∈ Z.edges) : DefectBridge G D s(a,p) := by
    by_cases hc : ∃ P : FacingCore G D M, s(a,p) ∈ P.core.edges
    · obtain ⟨P,hP⟩ := hc
      exact P.bridge hP
    · obtain ⟨q,hqa,hq⟩ := cycle_other_neighbor hz he
      have hUq : (optionGraph G D M).Adj p q := by simpa using Z.edges_subset_edgeSet hq
      rcases hUq.2 with h | h | ⟨P,hP⟩
      · exact (ho.no_option_turn hg hs hr hqa (Or.inl h)).elim
      · exact (ho.no_option_turn hg hs hr hqa (Or.inr h)).elim
      · exact ho.bridge_of_core hg hs hr P (P.core.fst_mem_support_of_mem_edges hP)
          (fun he => hc ⟨P,he⟩)
  rcases hU.2 with ⟨r,hr,ho⟩ | ⟨r,hr,ho⟩ | ⟨P,hP⟩
  · exact hcase hr ho he
  · simpa only [Sym2.eq_swap] using hcase hr ho (by simpa only [Sym2.eq_swap] using he)
  · exact P.bridge hP

end Se20Part
