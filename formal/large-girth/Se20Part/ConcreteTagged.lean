import Se20Part.OptionGraph

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

def armCandidates {V : Type*} (G : SimpleGraph V) (M : Set G.edgeSet)
    (r h : G.edgeSet) : Set G.edgeSet :=
  {d | d ∈ M ∧ ∃ A : DefectArm G r d, A.a ∈ h.val ∧ (L2 G).Adj h d}

theorem armCandidates_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 11) {M : Set G.edgeSet} (hm : IsMatching M)
    {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    2 ≤ Nat.card (armCandidates G M r h) := by
  obtain ⟨d,A,ha,hadj⟩ := problem_arm hd hm hr hh
  obtain ⟨d',B,hb,hbadj,hpar⟩ := problem_arm_avoiding_parent hd (fun _ => some A.p) hm hr hh
  have hpp : B.p ≠ A.p := by intro heq; apply hpar; simp [heq]
  have hne : d.val ≠ d'.val := by
    intro heq
    have hBp : B.p ∈ d.val.val := by rw [heq,B.edge]; simp
    rw [A.edge,Sym2.mem_iff] at hBp
    rcases hBp with hBp | hBp
    · exact hpp hBp
    · obtain ⟨w,hw,hBw⟩ := (B.layers hg).1.2
      have hAw := (A.layers hg).2.1 w hw
      rw [← hBp,hBw] at hAw
      norm_num at hAw
  have hsub : ({d.val,d'.val} : Set G.edgeSet) ⊆ armCandidates G M r h := by
    intro e he
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ⟨d.property,A,ha,hadj⟩
    · have heq : e = d'.val := Set.mem_singleton_iff.mp he
      subst e
      exact ⟨d'.property,B,hb,hbadj⟩
  have hc := Set.ncard_le_ncard hsub
  simpa only [Set.ncard_pair hne,← Nat.card_coe_set_eq] using hc

def problemCandidates {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet)
    (h : {h // Problem G D M h}) : Set G.edgeSet :=
  {d | ∃ r ∈ D, ProblemAt G M r h.val ∧ d ∈ armCandidates G M r h.val}

/-- The corrected Haxell remark for the actual geometric candidate sets.
The degree hypothesis is on the sigma type of tagged candidates. -/
theorem geometric_tagged_haxell_seed {V : Type} [Fintype V] (hax : Haxell)
    {G : SimpleGraph V} (hd : MaxDegreeFour G) (hg : GirthAtLeast G 11)
    (D M : Set G.edgeSet) (hs : Separated G 5 D) (hm : IsMatching M) (hdisj : Disjoint D M)
    (hdeg : DegreeLE (taggedConflictGraph G (problemCandidates G D M)) 1) :
    ∃ J : Set G.edgeSet, J ⊆ M ∧ IsInducedMatching J ∧
      (∀ d ∈ J, ∀ r ∈ D, ¬ (L2 G).Adj d r) ∧
      ∀ h, Problem G D M h → ∃ d ∈ J, (L2 G).Adj h d := by
  apply tagged_haxell_dominating_seed hax G D M (problemCandidates G D M)
  · intro h
    obtain ⟨r,hr,hh⟩ := h.property
    have hc := armCandidates_card hd hg hm (fun hrM => Set.disjoint_left.mp hdisj hr hrM) hh
    apply hc.trans
    have hsub : armCandidates G M r h.val ⊆ problemCandidates G D M h :=
      fun d hd => ⟨r,hr,hh,hd⟩
    simpa only [← Nat.card_coe_set_eq] using Set.ncard_le_ncard hsub
  · exact hdeg
  · intro h d hd
    obtain ⟨r,hr,_,hd,A,ha,hadj⟩ := hd
    refine ⟨hd,hadj,?_⟩
    intro r' hr'
    by_cases heq : r = r'
    · subst r'
      exact layers_avoid_root A.edge (A.layers hg).1 (A.layers hg).2
    · intro hconf
      have hwithin := layers_within A.edge (A.layers hg).1 (A.layers hg).2
      have hself : WithinFrom G 0 r' r' := fun v hv => ⟨v,hv,.nil,by simp⟩
      exact hs r hr r' hr' heq ((within_conflict_within hwithin hself hconf).mono (by decide))

end Se20Part
