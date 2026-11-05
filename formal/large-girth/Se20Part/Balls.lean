import Se20Part.Contraction

noncomputable section
open scoped Classical
namespace Se20Part
open SimpleGraph

/-- Endpoint distance at most k, using walks so disconnected pairs are never distance zero. -/
def EdgeWithin {V : Type*} (G : SimpleGraph V) (k : ℕ) (e f : G.edgeSet) : Prop :=
  ∃ x ∈ e.val, ∃ y ∈ f.val, ∃ p : G.Walk x y, p.length ≤ k

def edgeBall {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) (k : ℕ) : Set G.edgeSet :=
  {f | f ≠ e ∧ EdgeWithin G k e f}

abbrev Forward {V : Type*} (G : SimpleGraph V) (u v : V) :=
  {w : V // G.Adj v w ∧ w ≠ u}

def branchEdges {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ℕ → V → V → Finset G.edgeSet
  | 0, _, _ => ∅
  | n+1, u, v => Finset.univ.biUnion fun w : Forward G u v =>
      insert ⟨s(v,w.val),w.property.1⟩ (branchEdges G n v w.val)

def branchBound : ℕ → ℕ
  | 0 => 0
  | n+1 => 3 * (1 + branchBound n)

theorem forward_card_le_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (huv : G.Adj u v) :
    Fintype.card (Forward G u v) ≤ 3 := by
  let f : Forward G u v → G.neighborSet v := fun w => ⟨w.val, w.property.1⟩
  have hi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : G.neighborSet v => x.val) h)
  have hn : (⟨u,huv.symm⟩ : G.neighborSet v) ∉ Set.range f := by
    rintro ⟨w,hw⟩
    exact w.property.2 (congrArg (fun x : G.neighborSet v => x.val) hw)
  have hc := Fintype.card_lt_of_injective_of_notMem f hi hn
  rw [G.card_neighborSet_eq_degree] at hc
  have := hd v
  omega

theorem branchEdges_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) {u v : V} (huv : G.Adj u v) :
    (branchEdges G n u v).card ≤ branchBound n := by
  induction n generalizing u v with
  | zero => simp [branchEdges, branchBound]
  | succ n ih =>
    calc
      _ ≤ ∑ w : Forward G u v,
          (insert (⟨s(v,w.val),w.property.1⟩ : G.edgeSet) (branchEdges G n v w.val)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _w : Forward G u v, (1 + branchBound n) := by
        apply Finset.sum_le_sum
        intro w _
        exact (Finset.card_insert_le _ _).trans (by have := ih w.property.1; omega)
      _ ≤ 3 * (1 + branchBound n) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (forward_card_le_three hd huv)
      _ = _ := rfl

theorem branchEdges_mono {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) :
    Monotone (fun n => branchEdges G n u v) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing u v with
  | zero => simp [branchEdges]
  | succ n ih =>
    intro e he
    simp only [branchEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨w, hw⟩ := he
    refine ⟨w, ?_⟩
    rcases Finset.mem_insert.mp hw with hw | hw
    · exact Finset.mem_insert.mpr (Or.inl hw)
    · exact Finset.mem_insert.mpr (Or.inr (ih _ _ hw))

theorem path_incident_mem_branch {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v y : V} (huv : G.Adj u v) (p : G.Walk v y) (hp : p.IsPath)
    (hu : u ∉ p.support) (f : G.edgeSet) (hf : y ∈ f.val)
    (hne : f.val ≠ s(u,v)) : f ∈ branchEdges G (p.length+1) u v := by
  induction p generalizing u with
  | @nil v =>
    obtain ⟨z,hz⟩ := Sym2.mem_iff_exists.mp hf
    have hvz : G.Adj v z := by simpa [hz] using f.property
    have hzu : z ≠ u := by intro h; apply hne; simp [hz, h, Sym2.eq_swap]
    simp only [Walk.length_nil, branchEdges, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    refine ⟨⟨z,hvz,hzu⟩, Finset.mem_insert.mpr (Or.inl ?_)⟩
    exact Subtype.ext hz
  | @cons v w y hvw p ih =>
    have hpath := (Walk.cons_isPath_iff hvw p).mp hp
    have hwu : w ≠ u := by
      intro h
      apply hu
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inr (h ▸ p.start_mem_support)
    simp only [Walk.length_cons, branchEdges, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨⟨w,hvw,hwu⟩, ?_⟩
    by_cases he : f.val = s(v,w)
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext he))
    · exact Finset.mem_insert.mpr (Or.inr (ih hvw hpath.1 hpath.2 hf he))

/-- Any reachable endpoint admits a shortest approach that does not cross the root edge. -/
theorem shortest_edge_approach {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet} {k : ℕ}
    (h : EdgeWithin G k e f) :
    ∃ (x z y : V) (p : G.Walk x y), e.val = s(x,z) ∧ y ∈ f.val ∧
      p.IsPath ∧ p.length ≤ k ∧ z ∉ p.support := by
  let P (n : ℕ) := ∃ x ∈ e.val, ∃ y ∈ f.val, ∃ p : G.Walk x y, p.length = n
  have hex : ∃ n, P n := by
    obtain ⟨x,hx,y,hy,p,_⟩ := h
    exact ⟨p.length,x,hx,y,hy,p,rfl⟩
  obtain ⟨x,hx,y,hy,p,hp⟩ := Nat.find_spec hex
  obtain ⟨z,he⟩ := Sym2.mem_iff_exists.mp hx
  have hxz : G.Adj x z := by simpa [he] using e.property
  have hmin : ∀ (a : V), a ∈ e.val → ∀ (b : V), b ∈ f.val →
      ∀ q : G.Walk a b, p.length ≤ q.length := by
    intro a ha b hb q
    rw [hp]
    exact Nat.find_min' hex ⟨a,ha,b,hb,q,rfl⟩
  have hpath : p.IsPath := by
    exact p.isPath_of_length_eq_dist (by
      apply Nat.le_antisymm
      · obtain ⟨q,hq⟩ := p.reachable.exists_walk_length_eq_dist
        simpa [hq] using hmin x hx y hy q
      · exact G.dist_le p)
  have hlen : p.length ≤ k := by
    obtain ⟨a,ha,b,hb,q,hq⟩ := h
    exact (hmin a ha b hb q).trans hq
  refine ⟨x,z,y,p,he,hy,hpath,hlen,?_⟩
  intro hz
  have hzmem : z ∈ e.val := by simp [he]
  have hlo := hmin z hzmem y hy (p.dropUntil z hz)
  have hlt := p.length_dropUntil_lt_length hz hxz.ne.symm
  omega

theorem two_branchBound (n : ℕ) : 2 * branchBound n + 3 = 3^(n+1) := by
  induction n with
  | zero => norm_num [branchBound]
  | succ n ih =>
    rw [branchBound, pow_succ]
    nlinarith

/-- Section 2, Fact 3: the full finite-graph edge-ball bound. -/
theorem edgeBall_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (e : G.edgeSet) (k : ℕ) :
    Nat.card (edgeBall G e k) ≤ 3^(k+2)-3 := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := by
    rcases Sym2.mk_surjective e.val with ⟨⟨u,v⟩,h⟩
    exact ⟨u,v,h.symm⟩
  have huv : G.Adj u v := by simpa [he] using e.property
  have hs : (edgeBall G e k).toFinset ⊆
      branchEdges G (k+1) u v ∪ branchEdges G (k+1) v u := by
    intro f hf
    obtain ⟨hne,hclose⟩ := Set.mem_toFinset.mp hf
    obtain ⟨x,z,y,p,hxz,hy,hpath,hlen,hz⟩ := shortest_edge_approach hclose
    have hxzadj : G.Adj x z := by simpa [hxz] using e.property
    have hne' : f.val ≠ s(z,x) := by
      intro hfval
      apply hne
      exact Subtype.ext (by simpa [Sym2.eq_swap] using hfval.trans (by rw [hxz]; exact Sym2.eq_swap))
    have hmem := path_incident_mem_branch hxzadj.symm p hpath hz f hy hne'
    have hmem' := branchEdges_mono G z x (Nat.add_le_add_right hlen 1) hmem
    rcases Sym2.eq_iff.mp (hxz.symm.trans he) with h | h
    · exact Finset.mem_union_right _ (by simpa [h.1,h.2] using hmem')
    · exact Finset.mem_union_left _ (by simpa [h.1,h.2] using hmem')
  have hb := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have h1 := branchEdges_card_le hd (k+1) huv
  have h2 := branchEdges_card_le hd (k+1) huv.symm
  have heq := two_branchBound (k+1)
  change 2 * branchBound (k+1) + 3 = 3^(k+2) at heq
  have hc : Nat.card (edgeBall G e k) = (edgeBall G e k).toFinset.card := by
    simp only [Nat.card_eq_fintype_card, Set.toFinset_card]
  omega

theorem ball_constants :
    (3^3-3 : ℕ) = 24 ∧ (3^4-3 : ℕ) = 78 ∧ (3^5-3 : ℕ) = 240 ∧
    (3^6-3 : ℕ) = 726 ∧ (3^7-3 : ℕ) = 2184 ∧
    (3^8-3 : ℕ) = 6558 ∧ (3^9-3 : ℕ) = 19680 := by norm_num

end Se20Part
