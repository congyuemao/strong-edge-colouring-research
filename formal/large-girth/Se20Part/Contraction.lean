import Se20Part.Definitions

noncomputable section
open scoped Classical
namespace Se20Part
open SimpleGraph

theorem no_triangle {V : Type*} {G : SimpleGraph V} (hg : GirthAtLeast G 5)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p, Walk.isPath_def, hab.ne.symm, hbc.ne, hca.ne]
  have := hg a p hp
  norm_num [p] at this

theorem no_square {V : Type*} {G : SimpleGraph V} (hg : GirthAtLeast G 5)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p, Walk.isPath_def, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
  have := hg a p hp
  norm_num [p] at this

theorem matching_disjoint {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) {e f : G.edgeSet} (he : e ∈ M) (hf : f ∈ M)
    (hne : e ≠ f) {v : V} (hv : v ∈ f.val) : v ∉ e.val :=
  fun h => hne (hm he hf h hv)

theorem matching_conflict_iff {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) {e f : G.edgeSet} (he : e ∈ M) (hf : f ∈ M) :
    (L2 G).Adj e f ↔ ∃ v, v ∈ External G e ∧ v ∈ f.val := by
  constructor
  · rintro ⟨hne, u, hu, v, hv, huv⟩
    have hvn := matching_disjoint hm he hf hne hv
    refine ⟨v, ⟨hvn, u, hu, ?_⟩, hv⟩
    exact huv.resolve_left (fun h => hvn (h ▸ hu))
  · rintro ⟨v, ⟨hvn, u, hu, huv⟩, hv⟩
    refine ⟨?_, u, hu, v, hv, Or.inr huv⟩
    intro h
    exact hvn (h ▸ hv)

/-- A matching neighbor covers at most one external vertex; this is where girth 5 is needed. -/
theorem external_endpoint_unique {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 5) {e f : G.edgeSet} {v w : V}
    (hv : v ∈ External G e) (hw : w ∈ External G e)
    (hvf : v ∈ f.val) (hwf : w ∈ f.val) : v = w := by
  by_contra hvw
  have hfval := (Sym2.mem_and_mem_iff hvw).mp ⟨hvf, hwf⟩
  have hvwadj : G.Adj v w := by simpa [hfval] using f.property
  obtain ⟨hvn, a, hae, hav⟩ := hv
  obtain ⟨hwn, b, hbe, hbw⟩ := hw
  by_cases hab : a = b
  · subst b
    exact no_triangle hg hav hvwadj hbw.symm
  · have heval := (Sym2.mem_and_mem_iff hab).mp ⟨hae, hbe⟩
    have habadj : G.Adj a b := by simpa [heval] using e.property
    exact no_square hg hav hvwadj hbw.symm habadj.symm
      (fun h => hwn (h ▸ hae)) (fun h => hvn (h.symm ▸ hbe))

/-- Lemma 3.1(a), its exact degree equality. -/
theorem matching_degree_eq_covered_external {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hg : GirthAtLeast G 5) {M : Set G.edgeSet}
    (hm : IsMatching M) (e : M) :
    (ConflictGraph G M).degree e = Fintype.card ↥(External G e.val ∩ Covered M) := by
  let A := (ConflictGraph G M).neighborSet e
  let B := External G e.val ∩ Covered M
  have hex (f : A) : ∃ v, v ∈ External G e.val ∧ v ∈ f.val.val.val :=
    (matching_conflict_iff hm e.property f.val.property).mp f.property
  let map : A → B := fun f => ⟨(hex f).choose,
    (hex f).choose_spec.1, f.val.val, f.val.property, (hex f).choose_spec.2⟩
  have hinj : Function.Injective map := by
    intro f f' h
    apply Subtype.ext
    apply Subtype.ext
    apply hm f.val.property f'.val.property (hex f).choose_spec.2
    have hv : (hex f).choose = (hex f').choose := congrArg Subtype.val h
    rw [hv]
    exact (hex f').choose_spec.2
  have hsurj : Function.Surjective map := by
    intro v
    obtain ⟨f, hf, hvf⟩ := v.property.2
    have hadj := (matching_conflict_iff hm e.property hf).mpr ⟨v.val, v.property.1, hvf⟩
    let f' : A := ⟨⟨f, hf⟩, hadj⟩
    refine ⟨f', Subtype.ext ?_⟩
    exact external_endpoint_unique hg (hex f').choose_spec.1 v.property.1
      (hex f').choose_spec.2 hvf
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (Equiv.ofBijective map ⟨hinj, hsurj⟩)

theorem external_card_le_six {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (e : G.edgeSet) : Fintype.card (External G e) ≤ 6 := by
  obtain ⟨u, v, he⟩ : ∃ u v, e.val = s(u, v) := by
    have := Sym2.mk_surjective e.val
    rcases this with ⟨⟨u,v⟩, h⟩
    exact ⟨u,v,h.symm⟩
  have huv : G.Adj u v := by simpa [he] using e.property
  let s := (G.neighborFinset u).erase v
  let t := (G.neighborFinset v).erase u
  have hsub : (External G e).toFinset ⊆ s ∪ t := by
    intro w hw
    obtain ⟨hwn, a, ha, haw⟩ := (Set.mem_toFinset.mp hw)
    have hwu : w ≠ u := by intro h; apply hwn; simp [he, h]
    have hwv : w ≠ v := by intro h; apply hwn; simp [he, h]
    simp only [he, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_union_left _ (by simp [s, hwv, haw])
    · exact Finset.mem_union_right _ (by simp [t, hwu, haw])
  have hs : s.card = G.degree u - 1 := by
    exact Finset.card_erase_of_mem (by simpa using huv)
  have ht : t.card = G.degree v - 1 := by
    exact Finset.card_erase_of_mem (by simpa using huv.symm)
  have hb := (Finset.card_le_card hsub).trans (Finset.card_union_le s t)
  rw [hs, ht] at hb
  have hu := hd u
  have hv := hd v
  have hc : Fintype.card (External G e) = (External G e).toFinset.card := by simp
  omega

theorem matching_maxDegree_six {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5) {M : Set G.edgeSet}
    (hm : IsMatching M) : DegreeLE (ConflictGraph G M) 6 := by
  rw [degreeLE_iff]
  intro e
  have heq := matching_degree_eq_covered_external hg hm e
  apply heq.le.trans
  let f : ↥(External G e.val ∩ Covered M) → External G e.val :=
    fun v => ⟨v.val, v.property.1⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun v : External G e.val => v.val) h)
  exact (Fintype.card_le_of_injective f hf).trans (external_card_le_six hd e.val)

theorem matching_degree_eq_covered_external_nat {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hg : GirthAtLeast G 5) {M : Set G.edgeSet}
    (hm : IsMatching M) (e : M) :
    Nat.card ((ConflictGraph G M).neighborSet e) =
      Nat.card ↥(External G e.val ∩ Covered M) := by
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using
    matching_degree_eq_covered_external hg hm e

/-- Lift a simple path of matching edges, allowing arbitrary endpoints in its first/last edges. -/
theorem lift_matching_path {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) {e f : M} (p : (ConflictGraph G M).Walk e f)
    (hp : p.IsPath) {x y : V} (hx : x ∈ e.val.val) (hy : y ∈ f.val.val) :
    ∃ q : G.Walk x y, q.IsPath ∧ p.length ≤ q.length ∧ q.length ≤ 2 * p.length + 1 ∧
      ∀ z ∈ q.support, ∃ a ∈ p.support, z ∈ a.val.val := by
  induction p generalizing x with
  | @nil e =>
    by_cases hxy : x = y
    · subst y
      exact ⟨.nil, Walk.IsPath.nil, by simp, by simp, by
        intro z hz; simp only [Walk.support_nil, List.mem_singleton] at hz
        subst z; exact ⟨_, by simp, hx⟩⟩
    · have he := (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
      have hadj : G.Adj x y := by simpa [he] using e.val.property
      refine ⟨.cons hadj .nil, ?_, by simp, by simp, ?_⟩
      · simp [Walk.isPath_def, hxy]
      · intro z hz
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact ⟨_, by simp, hx⟩
        · exact ⟨_, by simp, hy⟩
  | @cons e a f hadj p ih =>
    have hpa := (Walk.cons_isPath_iff hadj p).mp hp
    obtain ⟨b, ⟨hbnot, c, hc, hcb⟩, hb⟩ :=
      (matching_conflict_iff hm e.property a.property).mp hadj
    obtain ⟨q, hq, hl, hu, hs⟩ := ih hpa.1 hb hy
    have hout (z : V) (hz : z ∈ e.val.val) : z ∉ q.support := by
      intro hzq
      obtain ⟨a', ha', hza'⟩ := hs z hzq
      have heq : e = a' := Subtype.ext (hm e.property a'.property hz hza')
      exact hpa.2 (heq ▸ ha')
    have hcq := hout c hc
    by_cases hxc : x = c
    · subst x
      refine ⟨.cons hcb q, hq.cons hcq, ?_, ?_, ?_⟩
      · simp only [Walk.length_cons]; omega
      · simp only [Walk.length_cons]; omega
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨e, by simp, hc⟩
        · obtain ⟨a', ha', hza'⟩ := hs z hz
          exact ⟨a', by simp [ha'], hza'⟩
    · have he := (Sym2.mem_and_mem_iff hxc).mp ⟨hx, hc⟩
      have hxcadj : G.Adj x c := by simpa [he] using e.val.property
      refine ⟨.cons hxcadj (.cons hcb q), (hq.cons hcq).cons ?_, ?_, ?_, ?_⟩
      · simpa using And.intro hxc (hout x hx)
      · simp only [Walk.length_cons]; omega
      · simp only [Walk.length_cons]; omega
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact ⟨e, by simp, hx⟩
        · exact ⟨e, by simp, hc⟩
        · obtain ⟨a', ha', hza'⟩ := hs z hz
          exact ⟨a', by simp [ha'], hza'⟩

/-- Lemma 3.1(b) in cycle-length form; no degree or girth-5 assumption is necessary. -/
theorem matching_cycle_lift {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) {e : M} (p : (ConflictGraph G M).Walk e e) (hp : p.IsCycle) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length ≤ 2 * p.length := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | cons hfa p =>
    rename_i a
    have hpath := (Walk.cons_isCycle_iff p hfa).mp hp
    obtain ⟨b, ⟨_, c, hc, hcb⟩, hb⟩ :=
      (matching_conflict_iff hm e.property a.property).mp hfa
    obtain ⟨q, hq, hl, hu, _⟩ := lift_matching_path hm p hpath.1 hb hc
    refine ⟨c, .cons hcb q, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨hq, ?_⟩
      intro hmem
      have hone := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
      have hthree := hp.three_le_length
      simp only [Walk.length_cons] at hthree
      omega
    · simp only [Walk.length_cons]
      omega

theorem matching_girth {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) {g : ℕ} (hg : GirthAtLeast G g) :
    GirthAtLeast (ConflictGraph G M) ((g + 1) / 2) := by
  intro e p hp
  obtain ⟨v, q, hq, hl⟩ := matching_cycle_lift hm p hp
  have := hg v q hq
  omega

/-- Extended-girth formulation, retaining infinity for acyclic graphs. -/
theorem matching_egirth {V : Type*} {G : SimpleGraph V} {M : Set G.edgeSet}
    (hm : IsMatching M) : G.egirth ≤ 2 * (ConflictGraph G M).egirth := by
  by_cases ha : (ConflictGraph G M).IsAcyclic
  · simp [ha.egirth_eq_top]
  · obtain ⟨e,p,hp,heq⟩ := SimpleGraph.exists_egirth_eq_length.mpr ha
    obtain ⟨v,q,hq,hl⟩ := matching_cycle_lift hm p hp
    calc
      G.egirth ≤ q.length := hq.egirth_le_length
      _ ≤ (2 * p.length : ℕ) := by exact_mod_cast hl
      _ = 2 * (ConflictGraph G M).egirth := by rw [heq]; norm_cast

end Se20Part
