import Se20Part.GeodesicProjection

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

/-- The family in Lemma 3.15. Its projections are actual nearest points, not
arbitrary labels; their metric characterization is `EdgeProjection.metric_minimal`. -/
structure SpanningFamily {V : Type*} {G : SimpleGraph V} {u v : V}
    (D : Set G.edgeSet) (Y : G.Walk u v) where
  edges : Set G.edgeSet
  finite : edges.Finite
  subset : edges ⊆ D
  projection : ∀ r : edges, EdgeProjection Y r.val
  positive : ∀ r, 1 ≤ (projection r).depth
  depth_le : ∀ r, (projection r).depth ≤ 5
  spans : ∀ j < Y.length, ∃ r r' : edges,
    (projection r).pos ≤ j ∧ j < (projection r').pos ∧
      (projection r).depth+(projection r').depth+
        ((projection r').pos-(projection r).pos) ≤ 7

theorem spanning_family_of_bridges {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} {g : ℕ} (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {Y : G.Walk u v}
    (hy : Y.IsPath) (hlen : 2*Y.length < g) {D : Set G.edgeSet}
    (hav : ∀ r ∈ D, ∀ x ∈ r.val, x ∉ Y.support)
    (hb : ∀ j < Y.length, DefectBridge G D s(Y.getVert j,Y.getVert (j+1))) :
    Nonempty (SpanningFamily D Y) := by
  let S : Set G.edgeSet := {r | r ∈ D ∧ ∃ P : EdgeProjection Y r, P.depth ≤ 5}
  choose P hP using fun r : S => r.property.2
  refine ⟨⟨S,Set.toFinite S,fun _ h => h.1,P,fun r => (P r).positive (hav _ r.property.1),hP,?_⟩⟩
  intro j hj
  obtain ⟨r,hr,r',hr',_,Q,Q',hQ,hQ',hpos,hpos',hbound⟩ := bridge_spans hg h42 hy hlen hav hj (hb j hj)
  let a : S := ⟨r,hr,Q,hQ⟩
  let b : S := ⟨r',hr',Q',hQ'⟩
  have heq := (P a).depth_pos_unique hg h42 hy hlen Q (by have := hP a; omega) (hav r hr)
  have heq' := (P b).depth_pos_unique hg h42 hy hlen Q' (by have := hP b; omega) (hav r' hr')
  exact ⟨a,b,by simpa [heq.2] using hpos,by simpa [heq'.2] using hpos',
    by simpa [heq.1,heq'.1,heq.2,heq'.2] using hbound⟩

theorem option_cycle_vertex_avoids {V : Type*} {G : SimpleGraph V}
    (hg : GirthAtLeast G 11) {D M : Set G.edgeSet} (hs : Separated G 5 D)
    {v x : V} {Z : (optionGraph G D M).Walk v v} (hz : Z.IsCycle)
    (hx : x ∈ Z.support) : x ∉ Covered D := by
  have hc := hz.ncard_neighborSet_toSubgraph_eq_two hx
  obtain ⟨y,hy⟩ : (Z.toSubgraph.neighborSet x).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  exact (optionGraph_avoids_defects hg hs (Z.toSubgraph.adj_sub hy)).1

/-- Lemma 3.15, including the nearest-point/depth spanning conclusion.
The support and edge containment hypotheses express that Y is a simple segment
of the given cycle; no assumption about spanning families is made. -/
theorem lemma_3_15 {V : Type*} [Fintype V] {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {D M : Set G.edgeSet}
    (hs : Separated G 5 D) {v u w : V}
    (Z : (optionGraph G D M).Walk v v) (hz : Z.IsCycle)
    (Y : G.Walk u w) (hy : Y.IsPath) (hlen : 2*Y.length < g)
    (hverts : Y.support ⊆ Z.support) (hedges : Y.edges ⊆ Z.edges) :
    Y.length = G.dist u w ∧ Nonempty (SpanningFamily D Y) := by
  have hg11 : GirthAtLeast G 11 := hg.mono (by omega)
  refine ⟨short_path_geodesic hg Y hy hlen,spanning_family_of_bridges hg h42 hy hlen ?_ ?_⟩
  · intro r hr x hx hxy
    exact option_cycle_vertex_avoids hg11 hs hz (hverts hxy) ⟨r,hr,hx⟩
  · intro j hj
    apply option_cycle_edge_bridge hg11 hs hz
    apply hedges
    exact (Y.adj_toSubgraph_iff_mem_edges).mp (Y.toSubgraph_adj_getVert hj)

/-- Keeping a shallowest edge at each occupied position preserves spanning.
This is the manuscript's reduction to at most one candidate at each position. -/
theorem SpanningFamily.distinct_positions {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y) :
    ∃ F' : SpanningFamily D Y, F'.edges ⊆ F.edges ∧
      Function.Injective (fun r => (F'.projection r).pos) := by
  letI : Finite F.edges := F.finite.to_subtype
  let pos : F.edges → ℕ := fun r => (F.projection r).pos
  let I := Set.range pos
  have hex (i : I) : ∃ r : F.edges, pos r = i.val ∧
      ∀ r' : F.edges, pos r' = i.val → (F.projection r).depth ≤ (F.projection r').depth := by
    have hne : {r : F.edges | pos r = i.val}.Nonempty := i.property
    exact Set.exists_min_image {r : F.edges | pos r = i.val}
      (fun r => (F.projection r).depth) (Set.toFinite _) hne
  choose pick hpick hmin using hex
  let S : Set G.edgeSet := Set.range (fun i : I => (pick i).val)
  have hsub : S ⊆ F.edges := by rintro _ ⟨i,rfl⟩; exact (pick i).property
  let lift : S → F.edges := fun r => ⟨r.val,hsub r.property⟩
  let proj : ∀ r : S, EdgeProjection Y r.val := fun r => F.projection (lift r)
  have hspan : ∀ j < Y.length, ∃ r r' : S,
      (proj r).pos ≤ j ∧ j < (proj r').pos ∧
        (proj r).depth+(proj r').depth+((proj r').pos-(proj r).pos) ≤ 7 := by
    intro j hj
    obtain ⟨r,r',hl,hr,hb⟩ := F.spans j hj
    let i : I := ⟨pos r,r,rfl⟩
    let i' : I := ⟨pos r',r',rfl⟩
    let a : S := ⟨(pick i).val,i,rfl⟩
    let b : S := ⟨(pick i').val,i',rfl⟩
    have ha : lift a = pick i := rfl
    have hb' : lift b = pick i' := rfl
    have hapos : (proj a).pos = (F.projection r).pos := hpick i
    have hbpos : (proj b).pos = (F.projection r').pos := hpick i'
    have had : (proj a).depth ≤ (F.projection r).depth := hmin i r rfl
    have hbd : (proj b).depth ≤ (F.projection r').depth := hmin i' r' rfl
    exact ⟨a,b,by omega,by omega,by omega⟩
  let F' : SpanningFamily D Y :=
    ⟨S,F.finite.subset hsub,fun r hr => F.subset (hsub hr),proj,
      fun r => F.positive (lift r),fun r => F.depth_le (lift r),hspan⟩
  refine ⟨F',hsub,?_⟩
  rintro ⟨r,i,rfl⟩ ⟨r',i',rfl⟩ heq
  have hii : i = i' := Subtype.ext ((hpick i).symm.trans (heq.trans (hpick i')))
  subst i'
  rfl

/-- The pairwise spacing inequality used by the transfer automaton follows from
actual endpoint-distance separation; it is not an extra geometric assumption. -/
theorem SpanningFamily.pair_spacing {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y)
    (hs : Separated G 5 D) (r r' : F.edges) (hne : r ≠ r') :
    5 ≤ (F.projection r).depth + (F.projection r').depth +
      Nat.dist (F.projection r).pos (F.projection r').pos := by
  let P := F.projection r
  let Q := F.projection r'
  let q := P.stem.append ((pathSegment Y P.pos Q.pos).append Q.stem.reverse)
  have hlen : q.length = P.depth+Q.depth+Nat.dist P.pos Q.pos := by
    simp only [q,Walk.length_append,Walk.length_reverse,P.length_stem,Q.length_stem,
      pathSegment_length Y P.pos_le Q.pos_le]
    omega
  by_contra! hsmall
  change P.depth+Q.depth+Nat.dist P.pos Q.pos < 5 at hsmall
  apply hs r.val (F.subset r.property) r'.val (F.subset r'.property)
    (fun h => hne (Subtype.ext h))
  exact ⟨P.endpoint,P.mem,Q.endpoint,Q.mem,q,by rw [hlen]; omega⟩

end Se20Part
