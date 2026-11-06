import fourth_pass.BitGraph

namespace Se20Fractional.FourthPass.Packed

/-- The finite bitmask semantics. It does not yet assert that every Lean graph
has been relabelled and encoded into one of the enumerated root profiles. -/
structure Model (n : Nat) (full : State) : Prop where
  valid : valid n full = true
  bounds : ∀ e ∈ full.chosen, e.1 < n ∧ e.2 < n
  edges : ∀ e ∈ full.chosen, adjacent n full.graph e.1 e.2 = true
  symm : ∀ a b, adjacent n full.graph a b = adjacent n full.graph b a
  irrefl : ∀ a, adjacent n full.graph a a = false
  conflicts : ∀ e ∈ full.chosen, ∀ f ∈ full.chosen, conflict n full.graph e f = true

def Boundary (n d h g : Nat) : Prop := ∀ a b, (a ≤ d ∨ b ≤ d) →
  adjacent n g a b = true → adjacent n h a b = true

structure Extends (n d : Nat) (st full : State) : Prop where
  subset : BitSubset st.graph full.graph
  symm : ∀ a, a < n → ∀ b, b < n → adjacent n st.graph a b = adjacent n st.graph b a
  boundary : Boundary n d st.graph full.graph
  chosen : ∀ e ∈ st.chosen, e ∈ full.chosen

theorem Boundary.mono {n d h k g : Nat} (hb : Boundary n d h g) (hk : BitSubset h k) :
    Boundary n d k g := by
  intro a b hab he
  exact adjacent_mono hk n a b (hb a b hab he)

theorem Model.degree {n : Nat} {full : State} (hm : Model n full) {a : Nat} (ha : a < n) :
    pop n (row n full.graph a) ≤ 4 := by
  have hv := hm.valid
  simp only [Se20Fractional.FourthPass.Packed.valid,Bool.and_eq_true,List.all_eq_true,
    decide_eq_true_eq] at hv
  exact hv.1 a (List.mem_range.mpr ha)

theorem conflict_missing_witness {n h g : Nat} {e f : Edge}
    (hg : conflict n g e f = true) (hh : conflict n h e f = false) :
    ∃ p ∈ [(e.1,f.1),(e.1,f.2),(e.2,f.1),(e.2,f.2)],
      adjacent n g p.1 p.2 = true ∧ adjacent n h p.1 p.2 = false := by
  have hn : ¬ conflict n h e f = true := by simp [hh]
  simp only [conflict_iff,not_or] at hn
  have hfalse {a b : Nat} (hp : ¬ adjacent n h a b = true) : adjacent n h a b = false :=
    Bool.eq_false_iff.mpr hp
  rcases (conflict_iff n g e f).mp hg with he | he | he | he | he | he | he | he
  · exact False.elim (hn.1 he)
  · exact False.elim (hn.2.1 he)
  · exact ⟨(e.1,f.1),by simp,he,hfalse hn.2.2.1⟩
  · exact ⟨(e.2,f.1),by simp,he,hfalse hn.2.2.2.1⟩
  · exact False.elim (hn.2.2.2.2.1 he)
  · exact False.elim (hn.2.2.2.2.2.1 he)
  · exact ⟨(e.1,f.2),by simp,he,hfalse hn.2.2.2.2.2.2.1⟩
  · exact ⟨(e.2,f.2),by simp,he,hfalse hn.2.2.2.2.2.2.2⟩

theorem witnesses_complete {n d h : Nat} {full : State} (hm : Model n full)
    (hh : BitSubset h full.graph) (hb : Boundary n d h full.graph)
    (hsymm : ∀ a, a < n → ∀ b, b < n → adjacent n h a b = adjacent n h b a)
    {e f : Edge} (he : e ∈ full.chosen) (hf : f ∈ full.chosen)
    (hc : conflict n h e f = false) :
    ∃ p ∈ witnesses n d h e f, adjacent n full.graph p.1 p.2 = true := by
  obtain ⟨p,hp,hpg,hph⟩ := conflict_missing_witness (hm.conflicts e he f hf) hc
  have hbounds : p.1 < n ∧ p.2 < n := by
    have heB := hm.bounds e he
    have hfB := hm.bounds f hf
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by omega,by omega⟩
  have hp1 : d < p.1 := by
    by_contra hn
    have ht := hb p.1 p.2 (Or.inl (by omega)) hpg
    simp [hph] at ht
  have hp2 : d < p.2 := by
    by_contra hn
    have ht := hb p.1 p.2 (Or.inr (by omega)) hpg
    simp [hph] at ht
  have hpne : p.1 ≠ p.2 := by
    intro heq
    rw [heq,hm.irrefl] at hpg
    contradiction
  have hpr : adjacent n full.graph p.2 p.1 = true := by rw [hm.symm]; exact hpg
  -- A missing edge at the first endpoint gives a strict degree inequality.
  have hd1 := row_degree_strict hh hpg hph
  have hdg1 := hm.degree hbounds.1
  have hphrev : adjacent n h p.2 p.1 = false := by
    rw [hsymm p.2 hbounds.2 p.1 hbounds.1]
    exact hph
  have hd2 := row_degree_strict hh hpr hphrev
  have hdg2 := hm.degree hbounds.2
  refine ⟨p,List.mem_filter.mpr ⟨hp,?_⟩,hpg⟩
  simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne]
  exact ⟨⟨⟨⟨hp1,hp2⟩,hpne⟩,by omega⟩,by omega⟩

theorem Extends.add_actual {n d : Nat} {st full : State} (hm : Model n full)
    (hs : Extends n d st full) {e : Edge} (he : adjacent n full.graph e.1 e.2 = true) :
    Extends n d ⟨addEdge n st.graph e,st.chosen⟩ full := by
  have her : adjacent n full.graph e.2 e.1 = true := by rw [hm.symm]; exact he
  have he1 := ((adjacent_iff n full.graph e.2 e.1).mp her).2
  have he2 := ((adjacent_iff n full.graph e.1 e.2).mp he).2
  exact ⟨addEdge_subset hs.subset he her,addEdge_symm hs.symm he1 he2,
    hs.boundary.mono (subset_addEdge n st.graph e),hs.chosen⟩

theorem Extends.valid {n d : Nat} {st full : State} (hm : Model n full)
    (hs : Extends n d st full) : valid n st = true :=
  valid_mono n hs.subset hs.chosen hm.valid

theorem forcePair_sound {n d : Nat} {st full : State} (hm : Model n full)
    (hs : Extends n d st full) {e f : Edge} (he : e ∈ full.chosen) (hf : f ∈ full.chosen) :
    ∃ g, forcePair n d (some st.graph) e f = some g ∧ Extends n d ⟨g,st.chosen⟩ full := by
  by_cases hc : conflict n st.graph e f = true
  · exact ⟨st.graph,by simp [forcePair,hc],hs⟩
  · have hc' : conflict n st.graph e f = false := Bool.eq_false_iff.mpr hc
    obtain ⟨p,hp,hpg⟩ := witnesses_complete hm hs.subset hs.boundary hs.symm he hf hc'
    cases hw : witnesses n d st.graph e f with
    | nil => simp [hw] at hp
    | cons a as =>
      cases as with
      | nil =>
        have hpa : p = a := by simpa [hw] using hp
        subst p
        exact ⟨addEdge n st.graph a,by simp [forcePair,hc',hw],hs.add_actual hm hpg⟩
      | cons b bs => exact ⟨st.graph,by simp [forcePair,hc',hw],hs⟩

theorem forceOne_sound {n d : Nat} {full : State} (hm : Model n full)
    (fs : List Edge) {e : Edge} (he : e ∈ full.chosen)
    (hfs : ∀ f ∈ fs, f ∈ full.chosen)
    (st : State) (hs : Extends n d st full) :
    ∃ g, forceOne n d e (some st.graph) fs = some g ∧ Extends n d ⟨g,st.chosen⟩ full := by
  induction fs generalizing st with
  | nil => exact ⟨st.graph,rfl,hs⟩
  | cons f fs ih =>
    obtain ⟨g,hg,hgs⟩ := forcePair_sound hm hs he (hfs f (by simp))
    obtain ⟨k,hk,hks⟩ := ih (fun f hf => hfs f (by simp [hf])) ⟨g,st.chosen⟩ hgs
    exact ⟨k,by simpa only [forceOne,hg] using hk,hks⟩

theorem forceAll_sound {n d : Nat} {full : State} (hm : Model n full)
    (qs : List Edge) (hqs : ∀ e ∈ qs, e ∈ full.chosen)
    (st : State) (hs : Extends n d st full) :
    ∃ g, forceAll n d (some st.graph) qs = some g ∧ Extends n d ⟨g,st.chosen⟩ full := by
  induction qs generalizing st with
  | nil => exact ⟨st.graph,rfl,hs⟩
  | cons e es ih =>
    have hes : ∀ f ∈ es, f ∈ full.chosen := fun f hf => hqs f (by simp [hf])
    obtain ⟨g,hg,hgs⟩ := forceOne_sound hm es (hqs e (by simp)) hes st hs
    obtain ⟨k,hk,hks⟩ := ih hes ⟨g,st.chosen⟩ hgs
    exact ⟨k,by simpa only [forceAll,hg] using hk,hks⟩

theorem propagate_sound {n d : Nat} {full : State} (hm : Model n full)
    (fuel : Nat) (st : State) (hs : Extends n d st full) :
    ∃ next, propagate n d fuel st = some next ∧ Extends n d next full := by
  induction fuel generalizing st with
  | zero => exact ⟨st,by simp [propagate,hs.valid hm],hs⟩
  | succ fuel ih =>
    obtain ⟨g,hg,hgs⟩ := forceAll_sound hm st.chosen hs.chosen st hs
    by_cases he : g = st.graph
    · subst g
      exact ⟨st,by simp [propagate,hs.valid hm,hg],hs⟩
    · obtain ⟨next,hn,hns⟩ := ih ⟨g,st.chosen⟩ hgs
      exact ⟨next,by simpa only [propagate,hs.valid hm,Bool.not_true,Bool.false_eq_true,
        ↓reduceIte,hg,beq_iff_eq,he] using hn,hns⟩

theorem extend_sound {n d : Nat} {full : State} (hm : Model n full)
    (st : State) (hs : Extends n d st full) {e : Edge} (he : e ∈ full.chosen) :
    ∃ next, extend n d st e = some next ∧ Extends n d next full := by
  have hgs := hs.add_actual hm (hm.edges e he)
  apply propagate_sound hm
  exact ⟨hgs.subset,hgs.symm,hgs.boundary,by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact hs.chosen f hf⟩

def Realizes (n d : Nat) (st : Option State) (full : State) : Prop :=
  Model n full ∧ ∃ s, st = some s ∧ Extends n d s full

/-- The actual bitmask search is sound for all finite bitmask models. The
remaining graph reduction must produce such a model in an enumerated profile. -/
theorem packed_search_sound (n d fuel need : Nat) (st : Option State) (cs : List Edge)
    (hcheck : selectionSearch (possible n d) (step n d) fuel need st cs = true) :
    ∀ full, Realizes n d st full →
      (cs.filter (fun e => decide (e ∈ full.chosen))).length < need := by
  apply selectionSearch_sound (possible n d) (step n d) (Realizes n d)
    (fun full e => decide (e ∈ full.chosen)) ?_ ?_ fuel need st cs hcheck
  · intro st full e hm he
    obtain ⟨hmodel,s,rfl,hs⟩ := hm
    obtain ⟨next,hn,_⟩ := extend_sound hmodel s hs (of_decide_eq_true he)
    simp [possible,hn]
  · intro st full e hm he
    obtain ⟨hmodel,s,rfl,hs⟩ := hm
    obtain ⟨next,hn,hns⟩ := extend_sound hmodel s hs (of_decide_eq_true he)
    exact ⟨hmodel,next,by simp [step,hn],hns⟩

#print axioms packed_search_sound

end Se20Fractional.FourthPass.Packed
