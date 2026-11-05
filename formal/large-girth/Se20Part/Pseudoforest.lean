import Se20Part.TreeLemma

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

/-- "At most one cycle" means that all simple cycles have the same edge set.
It is imposed separately in every connected component. -/
def IsPseudoforest {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ C : G.ConnectedComponent, ∀ u v : C.supp,
    ∀ (p : C.toSimpleGraph.Walk u u) (q : C.toSimpleGraph.Walk v v),
      p.IsCycle → q.IsCycle → p.edgeSet = q.edgeSet

theorem tree_parent_root {V : Type*} {G : SimpleGraph V} (ht : G.IsTree) (root : V) :
    ∃ parent : V → Option V, parent root = none ∧
      ∀ u v, G.Adj u v → parent u = some v ∨ parent v = some u := by
  choose p hp _ using fun v => ht.connected.exists_path_of_dist v root
  let parent : V → Option V := fun v => if v = root then none else some (p v).snd
  refine ⟨parent,by simp [parent],fun u v huv => ?_⟩
  by_cases hv : v ∈ (p u).support
  · have hu : u ≠ root := by
      intro hur
      have hn := (hp u).nil_iff_eq.mpr hur
      have hvu : v = u := by simpa only [Walk.nil_iff_support_eq.mp hn,List.mem_singleton] using hv
      exact huv.ne hvu.symm
    exact Or.inl (by simp [parent,hu,ht.isAcyclic.eq_snd_of_adj_start (hp u) huv hv])
  · have hvroot : v ≠ root := fun h => hv (h ▸ (p u).end_mem_support)
    have hpath : (Walk.cons huv.symm (p u)).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp u,hv⟩
    have heq : Walk.cons huv.symm (p u) = p v := congrArg Subtype.val
      ((ht.isAcyclic.subsingleton_path v root).elim ⟨_,hpath⟩ ⟨_,hp v⟩)
    exact Or.inr (by simp [parent,hvroot,← heq])

theorem one_cycle_parent {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (hunique : ∀ u v (p : G.Walk u u) (q : G.Walk v v),
      p.IsCycle → q.IsCycle → p.edgeSet = q.edgeSet) :
    ∃ parent : V → Option V, ∀ u v, G.Adj u v →
      parent u = some v ∨ parent v = some u := by
  by_cases hacyc : G.IsAcyclic
  · exact tree_parent ⟨hconn,hacyc⟩
  · obtain ⟨u,p,hp⟩ : ∃ u, ∃ p : G.Walk u u, p.IsCycle := by
      simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hacyc
    let e := s(u,p.snd)
    have he : e ∈ p.edgeSet := Walk.mk_start_snd_mem_edges hp.not_nil
    have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet he
    have hnbridge : ¬ G.IsBridge e := by
      intro hb
      exact (SimpleGraph.isBridge_iff_forall_cycle_notMem heG).mp hb p hp he
    let T := G.deleteEdges {e}
    have hTconn : T.Connected := hconn.preconnected.connected_deleteEdges_of_not_isBridge hnbridge
    have hTacyc : T.IsAcyclic := by
      intro v q hq
      let q' := q.mapLe (G.deleteEdges_le {e})
      have hq' : q'.IsCycle := hq.mapLe _
      have heq := hunique u v p q' hp hq'
      have heq' : e ∈ q.edgeSet := by
        have := heq ▸ he
        simpa only [q',Walk.edgeSet_mapLe_eq_edgeSet] using this
      have hmem := q.edges_subset_edgeSet heq'
      simpa [T,SimpleGraph.edgeSet_deleteEdges] using hmem
    obtain ⟨par,hroot,hpar⟩ := tree_parent_root ⟨hTconn,hTacyc⟩ u
    let parent : V → Option V := Function.update par u (some p.snd)
    refine ⟨parent,fun v w hvw => ?_⟩
    by_cases heq : s(v,w) = e
    · rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl (by simp [parent])
      · exact Or.inr (by simp [parent])
    · have hadj : T.Adj v w := by simpa [T,SimpleGraph.deleteEdges_adj] using And.intro hvw heq
      rcases hpar v w hadj with h | h
      · have hv : v ≠ u := by intro heq; subst v; simp [hroot] at h
        exact Or.inl (by simpa [parent,hv] using h)
      · have hw : w ≠ u := by intro heq; subst w; simp [hroot] at h
        exact Or.inr (by simpa [parent,hw] using h)

/-- Orient each tree component from a root, and each unicyclic component by
deleting a cycle edge, rooting at its endpoint, then restoring that edge. -/
theorem pseudoforest_parent {V : Type*} {G : SimpleGraph V} (h : IsPseudoforest G) :
    ∃ parent : V → Option V, ∀ u v, G.Adj u v →
      parent u = some v ∨ parent v = some u := by
  choose par hpar using fun C : G.ConnectedComponent =>
    one_cycle_parent C.connected_toSimpleGraph (h C)
  let lift (C : G.ConnectedComponent) (v : V) : Option V :=
    if hv : v ∈ C.supp then (par C ⟨v,hv⟩).map Subtype.val else none
  have hlift (C : G.ConnectedComponent) (u v : V) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
      (hadj : G.Adj u v) : lift C u = some v ∨ lift C v = some u := by
    rcases hpar C ⟨u,hu⟩ ⟨v,hv⟩ hadj with hp | hp
    · exact Or.inl (by simp only [lift,dif_pos hu,hp,Option.map_some])
    · exact Or.inr (by simp only [lift,dif_pos hv,hp,Option.map_some])
  refine ⟨fun v => lift (G.connectedComponentMk v) v,fun u v huv => ?_⟩
  have heq : G.connectedComponentMk u = G.connectedComponentMk v :=
    ConnectedComponent.sound huv.reachable
  change lift (G.connectedComponentMk u) u = some v ∨ lift (G.connectedComponentMk v) v = some u
  rw [← heq]
  exact hlift _ u v rfl heq.symm huv

end Se20Part
