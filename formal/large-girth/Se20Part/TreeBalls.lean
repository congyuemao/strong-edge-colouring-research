import Se20Part.TreeBallCodes

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
namespace TreeBall
set_option maxHeartbeats 2000000
attribute [local instance] forwardFintype

variable {V : Type} {G : SimpleGraph V}

def branches [G.LocallyFinite] (n : ℕ) (u v : V) : Finset G.edgeSet :=
  univ.image (codeEdge (G := G) (n := n) (u := u) (v := v))

theorem branches_card [G.LocallyFinite] (ht : G.IsAcyclic) (hd : ∀ v, G.degree v = 4)
    (n : ℕ) {u v : V} (h : G.Adj u v) : (branches (G := G) n u v).card = branchBound n := by
  rw [branches,card_image_of_injective _ (codeEdge_injective ht n h),card_univ,code_card hd n h]

theorem mem_branches_succ [G.LocallyFinite] {n : ℕ} {u v : V} (e : G.edgeSet) :
    e ∈ branches (n+1) u v ↔
      ∃ w : Forward G u v, e = ⟨s(v,w.val),w.property.1⟩ ∨ e ∈ branches n v w.val := by
  constructor
  · intro he
    obtain ⟨⟨w,none|c⟩,_,hc⟩ := mem_image.mp he
    · exact ⟨w,Or.inl hc.symm⟩
    · exact ⟨w,Or.inr (mem_image.mpr ⟨c,mem_univ _,hc⟩)⟩
  · rintro ⟨w,he|he⟩
    · exact mem_image.mpr ⟨⟨w,none⟩,mem_univ _,he.symm⟩
    · obtain ⟨c,_,hc⟩ := mem_image.mp he
      exact mem_image.mpr ⟨⟨w,some c⟩,mem_univ _,hc⟩

theorem branches_mono [G.LocallyFinite] (u v : V) : Monotone (fun n => branches (G := G) n u v) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing u v with
  | zero => simp [branches,Code]
  | succ n ih =>
    intro e he
    obtain ⟨w,hw⟩ := (mem_branches_succ e).mp he
    exact (mem_branches_succ e).mpr ⟨w,hw.imp_right (fun hh => ih _ _ hh)⟩

theorem path_incident_mem [G.LocallyFinite] {u v y : V} (h : G.Adj u v)
    (p : G.Walk v y) (hp : p.IsPath) (hu : u ∉ p.support) (e : G.edgeSet)
    (he : y ∈ e.val) (hne : e.val ≠ s(u,v)) : e ∈ branches (p.length+1) u v := by
  induction p generalizing u with
  | @nil v =>
    obtain ⟨z,hz⟩ := Sym2.mem_iff_exists.mp he
    have hvz : G.Adj v z := by simpa [hz] using e.property
    have hzu : z ≠ u := by intro heq; apply hne; simp [hz,heq,Sym2.eq_swap]
    exact (mem_branches_succ e).mpr ⟨⟨z,hvz,hzu⟩,Or.inl (Subtype.ext hz)⟩
  | @cons v w y hvw p ih =>
    have hh := (Walk.cons_isPath_iff hvw p).mp hp
    have hwu : w ≠ u := by intro heq; apply hu; simp only [Walk.support_cons,List.mem_cons]; exact Or.inr (heq ▸ p.start_mem_support)
    apply (mem_branches_succ e).mpr
    refine ⟨⟨w,hvw,hwu⟩,?_⟩
    by_cases heq : e.val = s(v,w)
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr (ih hvw hh.1 hh.2 he heq)

theorem codeEdge_ne_root (ht : G.IsAcyclic) {n : ℕ} {u v : V} (h : G.Adj u v)
    (c : Code G n u v) : (codeEdge c).val ≠ s(u,v) := by
  intro he
  let p : RootPath G u := ⟨v,h.toWalk,by simp [h.ne],by simp⟩
  have hh := pathEdge_injective ht u (show pathEdge (codePath ht h c) = pathEdge p by
    rw [← codeEdge_pathEdge]; exact Subtype.ext he)
  have hl := congrArg (fun p : RootPath G u => p.2.val.length) hh
  have hc := (codeWalk_length h c).1
  change (codeWalk h c).length = 1 at hl
  omega

theorem codeEdge_approach {n : ℕ} {u v : V} (c : Code G n u v) :
    ∃ y ∈ (codeEdge c).val, ∃ p : G.Walk v y, p.length < n := by
  induction n generalizing u v with
  | zero => exact isEmptyElim c
  | succ n ih =>
    rcases c with ⟨w,none|c⟩
    · exact ⟨v,by simp [codeEdge],Walk.nil,by simp⟩
    · obtain ⟨y,hy,p,hp⟩ := ih c
      exact ⟨y,hy,Walk.cons w.property.1 p,by simp only [Walk.length_cons]; omega⟩

theorem opposite_edges_ne (ht : G.IsAcyclic) {n m : ℕ} {u v : V} (h : G.Adj u v)
    (a : Code G n u v) (b : Code G m v u) : codeEdge a ≠ codeEdge b := by
  cases m with
  | zero => exact isEmptyElim b
  | succ m =>
    rcases b with ⟨w,none|b⟩
    · intro he
      let p : RootPath G u := ⟨w.val,w.property.1.toWalk,by simp [w.property.1.ne],by simp⟩
      have hp := pathEdge_injective ht u (show pathEdge (codePath ht h a) = pathEdge p by
        rw [← codeEdge_pathEdge]
        exact he)
      have hl := congrArg (fun q : RootPath G u => q.2.val.length) hp
      have ha := (codeWalk_length h a).1
      change (codeWalk h a).length = 1 at hl
      omega
    · intro he
      have hp := pathEdge_injective ht u (show pathEdge (codePath ht h a) = pathEdge (codePath ht w.property.1 b) by
        simpa only [← codeEdge_pathEdge,codeEdge] using he)
      have hh := congrArg (fun q : RootPath G u => q.2.val.snd) hp
      simp only [codePath,codeWalk_snd] at hh
      exact w.property.2 hh.symm

theorem branches_disjoint [G.LocallyFinite] (ht : G.IsAcyclic) (n m : ℕ) {u v : V}
    (h : G.Adj u v) : Disjoint (branches (G := G) n u v) (branches m v u) := by
  apply Finset.disjoint_left.mpr
  intro e ha hb
  obtain ⟨a,_,ha⟩ := mem_image.mp ha
  obtain ⟨b,_,hb⟩ := mem_image.mp hb
  exact opposite_edges_ne ht h a b (ha.trans hb.symm)

theorem edgeBall_eq [G.LocallyFinite] (ht : G.IsAcyclic) (e : G.edgeSet) (k : ℕ)
    {u v : V} (he : e.val = s(u,v)) :
    edgeBall G e k = (↑(branches (G := G) (k+1) u v ∪ branches (k+1) v u) : Set G.edgeSet) := by
  have huv : G.Adj u v := by simpa [he] using e.property
  ext f
  constructor
  · rintro ⟨hne,hclose⟩
    obtain ⟨x,z,y,p,hxz,hy,hp,hlen,hz⟩ := shortest_edge_approach hclose
    have hxzadj : G.Adj x z := by simpa [hxz] using e.property
    have hne' : f.val ≠ s(z,x) := by
      intro hfv
      apply hne
      exact Subtype.ext (by rw [hfv,hxz,Sym2.eq_swap])
    have hf := path_incident_mem hxzadj.symm p hp hz f hy hne'
    have hf' := branches_mono z x (Nat.add_le_add_right hlen 1) hf
    rcases Sym2.eq_iff.mp (hxz.symm.trans he) with h | h
    · exact mem_union_right _ (by simpa only [h.1,h.2] using hf')
    · exact mem_union_left _ (by simpa only [h.1,h.2] using hf')
  · intro hf
    rcases mem_union.mp hf with hf | hf
    · obtain ⟨c,_,rfl⟩ := mem_image.mp hf
      obtain ⟨y,hy,p,hp⟩ := codeEdge_approach c
      exact ⟨fun hh => codeEdge_ne_root ht huv c (by rw [hh,he]),
        v,by simp [he],y,hy,p,by omega⟩
    · obtain ⟨c,_,rfl⟩ := mem_image.mp hf
      obtain ⟨y,hy,p,hp⟩ := codeEdge_approach c
      exact ⟨fun hh => codeEdge_ne_root ht huv.symm c (by rw [hh,he,Sym2.eq_swap]),
        u,by simp [he],y,hy,p,by omega⟩

theorem edgeBall_card [G.LocallyFinite] (ht : G.IsAcyclic) (hd : ∀ v, G.degree v = 4)
    (e : G.edgeSet) (k : ℕ) : Nat.card (edgeBall G e k) = 3^(k+2)-3 := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  have huv : G.Adj u v := by simpa [← he] using e.property
  rw [edgeBall_eq ht e k he.symm]
  rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
  simp only [Finset.toFinset_coe]
  rw [card_union_of_disjoint (branches_disjoint ht _ _ huv),branches_card ht hd _ huv,
    branches_card ht hd _ huv.symm]
  have hh := two_branchBound (k+1)
  change 2*branchBound (k+1)+3 = 3^(k+2) at hh
  omega

end TreeBall

/-- Exact Section 2 ball size in the genuine infinite four-regular tree. -/
theorem infinite_four_tree_edgeBall_card (T : InfiniteFourTree) (e : T.graph.edgeSet) (k : ℕ) :
    Nat.card (edgeBall T.graph e k) = 3^(k+2)-3 := by
  letI : T.graph.LocallyFinite := fun v => (T.finite_neighbors v).fintype
  apply TreeBall.edgeBall_card T.isTree.isAcyclic
  intro v
  simpa only [Nat.card_eq_fintype_card,T.graph.card_neighborSet_eq_degree] using T.degree_four v

end Se20Part
