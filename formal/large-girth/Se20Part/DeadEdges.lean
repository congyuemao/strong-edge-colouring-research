import Se20Part.TheoremB

noncomputable section
open scoped Classical
open SimpleGraph Finset
namespace Se20Part

theorem walk_inside_edge {V : Type*} {G : SimpleGraph V} (e : G.edgeSet)
    {x y : V} (hx : x ∈ e.val) (hy : y ∈ e.val) :
    ∃ p : G.Walk x y, p.length ≤ 1 ∧ ∀ z ∈ p.support, z ∈ e.val := by
  by_cases hxy : x = y
  · subst y
    exact ⟨.nil, by simp, by simpa using hx⟩
  · have he := (Sym2.mem_and_mem_iff hxy).mp ⟨hx,hy⟩
    have hadj : G.Adj x y := by simpa [he] using e.property
    exact ⟨hadj.toWalk, by simp, by simp [he]⟩

theorem conflict_walk {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet}
    (h : (L2 G).Adj e f) {x y : V} (hx : x ∈ e.val) (hy : y ∈ f.val) :
    ∃ p : G.Walk x y, p.length ≤ 3 ∧
      ∀ z ∈ p.support, z ∈ e.val ∨ z ∈ f.val := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := h
  obtain ⟨p,hp,hps⟩ := walk_inside_edge e hx ha
  obtain ⟨q,hq,hqs⟩ := walk_inside_edge f hb hy
  rcases hab with rfl | hab
  · refine ⟨p.append q, by simp; omega, ?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff p q).mp hz with hz | hz
    · exact Or.inl (hps z hz)
    · exact Or.inr (hqs z hz)
  · refine ⟨p.append (hab.toWalk.append q), by simp; omega, ?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff p _).mp hz with hz | hz
    · exact Or.inl (hps z hz)
    · rcases (Walk.mem_support_append_iff hab.toWalk q).mp hz with hz | hz
      · simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact Or.inl ha
        · exact Or.inr hb
      · exact Or.inr (hqs z hz)

/-- Connect two matching neighbors through a common defect; the length is at most five. -/
theorem common_killer_walk {V : Type*} {G : SimpleGraph V} {f f' r : G.edgeSet}
    (hfr : (L2 G).Adj f r) (hf'r : (L2 G).Adj f' r)
    {o o' : V} (ho : o ∈ f.val) (ho' : o' ∈ f'.val) :
    ∃ p : G.Walk o o', p.length ≤ 5 ∧
      ∀ z ∈ p.support, z ∈ f.val ∨ z ∈ r.val ∨ z ∈ f'.val := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := hf'r
  obtain ⟨p,hp,hps⟩ := conflict_walk hfr ho hb
  obtain ⟨q,hq,hqs⟩ := walk_inside_edge f' ha ho'
  rcases hab with rfl | hab
  · refine ⟨p.append q, by simp; omega, ?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff p q).mp hz with hz | hz
    · exact (hps z hz).imp_right Or.inl
    · exact Or.inr (Or.inr (hqs z hz))
  · refine ⟨p.append (hab.symm.toWalk.append q), by simp; omega, ?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff p _).mp hz with hz | hz
    · exact (hps z hz).imp_right Or.inl
    · rcases (Walk.mem_support_append_iff hab.symm.toWalk q).mp hz with hz | hz
      · simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inr (hqs z hz))

theorem path_forces_vertex {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {o o' : V} (p q : G.Walk o o')
    (hp : p.IsPath) (hl : p.length + q.length < g) {v : V} (hv : v ∈ p.support) :
    v ∈ q.support := by
  have h := short_paths_unique hg hp q.bypass_isPath
    (by have := q.length_bypass_le_length; omega)
  exact q.support_bypass_subset_support (h ▸ hv)

/-- If two covered neighbors of one vertex have a common killer, that killer
contains the vertex. This needs girth eight. -/
theorem common_killer_contains_vertex {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 8) {v o o' : V} (hvo : G.Adj v o) (hvo' : G.Adj v o')
    (hoo' : o ≠ o') {f f' r : G.edgeSet} (ho : o ∈ f.val) (ho' : o' ∈ f'.val)
    (hvf : v ∉ f.val) (hvf' : v ∉ f'.val)
    (hfr : (L2 G).Adj f r) (hf'r : (L2 G).Adj f' r) : v ∈ r.val := by
  obtain ⟨q,hq,hqs⟩ := common_killer_walk hfr hf'r ho ho'
  let p := Walk.cons hvo.symm (Walk.cons hvo' .nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hvo.ne.symm, hvo'.ne, hoo']
  have hv : v ∈ q.support := path_forces_vertex hg p q hp (by simp only [p, Walk.length_cons, Walk.length_nil]; omega) (by simp [p])
  exact (hqs v hv).resolve_left hvf |>.resolve_right hvf'

/-- Across the two ends of a matching edge the same argument needs girth nine. -/
theorem common_killer_meets_edge {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 9) {M : Set G.edgeSet} (hm : IsMatching M)
    {h f f' r : G.edgeSet} (hh : h ∈ M) (hf : f ∈ M) (hf' : f' ∈ M)
    {o o' : V} (ho : o ∈ External G h) (ho' : o' ∈ External G h)
    (hoo' : o ≠ o') (hof : o ∈ f.val) (ho'f' : o' ∈ f'.val)
    (hfr : (L2 G).Adj f r) (hf'r : (L2 G).Adj f' r) :
    ∃ v, v ∈ h.val ∧ v ∈ r.val := by
  obtain ⟨hno,u,hu,huo⟩ := ho
  obtain ⟨hno',v,hv,hvo'⟩ := ho'
  have hfh : f ≠ h := fun heq => hno (heq ▸ hof)
  have hf'h : f' ≠ h := fun heq => hno' (heq ▸ ho'f')
  have huof : u ∉ f.val := matching_disjoint hm hf hh hfh hu
  have huof' : u ∉ f'.val := matching_disjoint hm hf' hh hf'h hu
  by_cases huv : u = v
  · subst v
    exact ⟨u,hu,common_killer_contains_vertex (hg.mono (by decide)) huo hvo' hoo'
      hof ho'f' huof huof' hfr hf'r⟩
  · have he := (Sym2.mem_and_mem_iff huv).mp ⟨hu,hv⟩
    have huvAdj : G.Adj u v := by simpa [he] using h.property
    obtain ⟨q,hq,hqs⟩ := common_killer_walk hfr hf'r hof ho'f'
    let p := Walk.cons huo.symm (Walk.cons huvAdj (Walk.cons hvo' .nil))
    have hp : p.IsPath := by
      have hou : o ≠ u := fun heq => hno (heq ▸ hu)
      have hov : o ≠ v := fun heq => hno (heq ▸ hv)
      have ho'u : o' ≠ u := fun heq => hno' (heq ▸ hu)
      have ho'v : o' ≠ v := fun heq => hno' (heq ▸ hv)
      simp [p, Walk.isPath_def, hou, hov, hoo', huv, ho'u.symm, ho'v.symm]
    have huq : u ∈ q.support := path_forces_vertex hg p q hp
      (by simp only [p, Walk.length_cons, Walk.length_nil]; omega) (by simp [p])
    exact ⟨u,hu,(hqs u huq).resolve_left huof |>.resolve_right huof'⟩

/-- Lemma 3.9(b), at the corrected girth threshold nine. -/
theorem dead_edge_b : DeadEdgeBStatement := by
  intro V _ G hd hg D M hD hm hdisj h hdead hends
  obtain ⟨r,hr,hprob⟩ := hdead.1
  have hsix := hprob.2.2.1
  let X := External G h
  have hchoice : ∀ o : X, ∃ f ∈ M, o.val ∈ f.val ∧ (L2 G).Adj h f := by
    intro o
    obtain ⟨f,hf,hof⟩ := hprob.2.2.2 o.property
    exact ⟨f,hf,hof,(matching_conflict_iff hm hprob.1 hf).mpr ⟨o.val,o.property,hof⟩⟩
  choose f hf hof hhf using hchoice
  have hkill : ∀ o : X, ∃ r ∈ D, (L2 G).Adj (f o) r := by
    intro o
    exact (hdead.2 (f o) (hf o) (hhf o)).2
  choose k hk hfk using hkill
  let target := {r : G.edgeSet // r ∈ D ∧ ∃ f ∈ M, (L2 G).Adj h f ∧ (L2 G).Adj f r}
  let pick : X → target := fun o => ⟨k o,hk o,f o,hf o,hhf o,hfk o⟩
  have hinj : Function.Injective pick := by
    intro o o' heq
    by_contra hne
    have hkk : k o = k o' := congrArg Subtype.val heq
    obtain ⟨v,hvh,hvk⟩ := common_killer_meets_edge hg hm hprob.1 (hf o) (hf o')
      o.property o'.property (fun h => hne (Subtype.ext h)) (hof o) (hof o')
      (hfk o) (hkk ▸ hfk o')
    exact hends v hvh ⟨k o,hk o,hvk⟩
  have hc := Nat.card_le_card_of_injective pick hinj
  exact hsix ▸ hc

theorem conflict_walk_to_edge {V : Type*} {G : SimpleGraph V} {e r : G.edgeSet}
    (h : (L2 G).Adj e r) {o : V} (ho : o ∈ e.val) :
    ∃ x ∈ r.val, ∃ p : G.Walk o x, p.length ≤ 2 := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := h
  obtain ⟨p,hp,_⟩ := walk_inside_edge e ho ha
  rcases hab with rfl | hab
  · exact ⟨a,hb,p,by omega⟩
  · exact ⟨b,hb,p.append hab.toWalk,by simp; omega⟩

theorem not_killer_of_two_step {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 6) {v o x : V} (hvo : G.Adj v o) (hvx : G.Adj v x)
    (hox : o ≠ x) {f r : G.edgeSet} (ho : o ∈ f.val) (hx : x ∈ r.val)
    (hvf : v ∉ f.val) (hvr : v ∉ r.val) : ¬ (L2 G).Adj f r := by
  intro hfr
  obtain ⟨q,hq,hqs⟩ := conflict_walk hfr ho hx
  let p := Walk.cons hvo.symm (Walk.cons hvx .nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hvo.ne.symm, hvx.ne, hox]
  have hv := path_forces_vertex hg p q hp
    (by simp only [p, Walk.length_cons, Walk.length_nil]; omega)
    (show v ∈ p.support by simp [p])
  exact (hqs v hv).elim hvf hvr

theorem three_other_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (huv : G.Adj u v) (hd : G.degree v = 4) :
    Nat.card {o // G.Adj v o ∧ o ≠ u} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : Finset.univ.filter (fun o => G.Adj v o ∧ o ≠ u) =
      (G.neighborFinset v).erase u := by ext o; simp [and_comm]
  rw [heq, Finset.card_erase_of_mem (by simpa using huv.symm), G.card_neighborFinset_eq_degree, hd]

/-- Lemma 3.9(a); the three killers are distinct from the incident defect and
lie within endpoint-distance four of it. -/
theorem dead_edge_a : DeadEdgeAStatement := by
  intro V _ G hd hg D M hD hm hdisj h hdead r hr hmeet
  obtain ⟨r₀,hr₀,hprob⟩ := hdead.1
  obtain ⟨u,huh,hur⟩ := hmeet
  obtain ⟨v,he⟩ := Sym2.mem_iff_exists.mp huh
  have huv : G.Adj u v := by simpa [he] using h.property
  have hvh : v ∈ h.val := by simp [he]
  have hnr : h ≠ r := fun h' => Set.disjoint_left.mp hdisj hr (h' ▸ hprob.1)
  have hvr : v ∉ r.val := by
    intro hvr
    exact hnr (Subtype.ext (he.trans ((Sym2.mem_and_mem_iff huv.ne).mp ⟨hur,hvr⟩).symm))
  let X := {o // G.Adj v o ∧ o ≠ u}
  have hcard : Nat.card X = 3 := three_other_neighbors huv (external_six_endpoint_degree hd hprob.2.2.1 hvh)
  have hchoice : ∀ o : X, ∃ f ∈ M, o.val ∈ f.val ∧ (L2 G).Adj h f ∧ v ∉ f.val := by
    intro o
    have ho : o.val ∈ External G h := by
      refine ⟨?_,v,hvh,o.property.1⟩
      simp [he, Sym2.mem_iff, o.property.2, o.property.1.ne.symm]
    obtain ⟨f,hf,hof⟩ := hprob.2.2.2 ho
    have hfh : f ≠ h := fun heq => ho.1 (heq ▸ hof)
    exact ⟨f,hf,hof,(matching_conflict_iff hm hprob.1 hf).mpr ⟨o.val,ho,hof⟩,
      matching_disjoint hm hf hprob.1 hfh hvh⟩
  choose f hf hof hhf hvf using hchoice
  have hkill : ∀ o : X, ∃ r' ∈ D, (L2 G).Adj (f o) r' :=
    fun o => (hdead.2 (f o) (hf o) (hhf o)).2
  choose k hk hfk using hkill
  have hkr (o : X) : k o ≠ r := by
    intro heq
    exact not_killer_of_two_step (hg.mono (by decide)) o.property.1 huv.symm
      o.property.2 (hof o) hur (hvf o) hvr (heq ▸ hfk o)
  have hnear (o : X) : EdgeWithin G 4 r (k o) := by
    obtain ⟨x,hx,p,hp⟩ := conflict_walk_to_edge (hfk o) (hof o)
    exact ⟨u,hur,x,hx,.cons huv (.cons o.property.1 p),by simp; omega⟩
  let target := {r' : G.edgeSet // r' ∈ D ∧ r' ≠ r ∧ EdgeWithin G 4 r r' ∧
      ∃ f ∈ M, (L2 G).Adj h f ∧ (L2 G).Adj f r'}
  let pick : X → target := fun o => ⟨k o,hk o,hkr o,hnear o,f o,hf o,hhf o,hfk o⟩
  have hinj : Function.Injective pick := by
    intro o o' heq
    by_contra hne
    have hkk : k o = k o' := congrArg Subtype.val heq
    have hvk := common_killer_contains_vertex hg o.property.1 o'.property.1
      (fun h => hne (Subtype.ext h)) (hof o) (hof o') (hvf o) (hvf o')
      (hfk o) (hkk ▸ hfk o')
    exact hD hr (hk o) ⟨(hkr o).symm,u,hur,v,hvk,Or.inr huv⟩
  have hc := Nat.card_le_card_of_injective pick hinj
  exact hcard ▸ hc

/-- Corollary 3.10 uses only girth six, rather than either full dead-edge count. -/
theorem no_dead_edges : NoDeadEdgesStatement := by
  intro V _ G hd hg D M hs hm hdisj h hdead
  obtain ⟨r,hr,hprob⟩ := hdead.1
  have hrM : r ∉ M := fun h => Set.disjoint_left.mp hdisj hr h
  obtain ⟨w,z,a,hrz,hah,hwa,haz⟩ := problem_branch hrM hprob
  have har : a ∉ r.val := by simp [hrz, Sym2.mem_iff, hwa.ne.symm, haz]
  obtain ⟨b,hhab⟩ := Sym2.mem_iff_exists.mp hah
  have hdeg := external_six_endpoint_degree hd hprob.2.2.1 hah
  have hex : ∃ o ∈ G.neighborFinset a, o ∉ ({w,b} : Finset V) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have hc : ({w,b} : Finset V).card ≤ 2 := by
      calc
        _ ≤ ({b} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    rw [G.card_neighborFinset_eq_degree, hdeg]
    omega
  obtain ⟨o,hoa,hn⟩ := hex
  have hao : G.Adj a o := by simpa using hoa
  have how : o ≠ w := by simpa using (not_or.mp (by simpa using hn)).1
  have hob : o ≠ b := by simpa using (not_or.mp (by simpa using hn)).2
  have hoe : o ∈ External G h := by
    refine ⟨?_,a,hah,hao⟩
    simp [hhab, Sym2.mem_iff, hao.ne.symm, hob]
  obtain ⟨f,hf,hof⟩ := hprob.2.2.2 hoe
  have hfh : f ≠ h := fun heq => hoe.1 (heq ▸ hof)
  have hconf := (matching_conflict_iff hm hprob.1 hf).mpr ⟨o,hoe,hof⟩
  obtain ⟨r',hr',hfr'⟩ := (hdead.2 f hf hconf).2
  have hne : r ≠ r' := by
    intro heq
    apply not_killer_of_two_step hg hao hwa.symm how hof (show w ∈ r.val by simp [hrz])
      (matching_disjoint hm hf hprob.1 hfh hah) har
    exact heq ▸ hfr'
  obtain ⟨x,hx,p,hp⟩ := conflict_walk_to_edge hfr' hof
  exact hs r hr r' hr' hne ⟨w,by simp [hrz],x,hx,
    .cons hwa (.cons hao p),by simp; omega⟩

end Se20Part
