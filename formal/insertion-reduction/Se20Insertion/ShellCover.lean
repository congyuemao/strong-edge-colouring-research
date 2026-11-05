import Se20Insertion.ShellChains

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Only the absence of triangles and squares through uv is needed here. -/
def LocallyTreeAt (u v : V) : Prop :=
  (∀ w, G.Adj u w → G.Adj v w → False) ∧
  (∀ x y, G.Adj u x → G.Adj x y → G.Adj y v → x = v ∨ y = u)

theorem locallyTreeAt_of_girth (hg : 7 ≤ G.egirth) {u v : V} (huv : G.Adj u v) :
    LocallyTreeAt G u v := by
  constructor
  · intro w huw hvw
    exact GirthGeometry.no_triangle hg huv hvw huw.symm
  · intro x y hux hxy hyv
    exact (GirthGeometry.square_backtrack hg hux hxy hyv huv.symm).symm.imp id Eq.symm

theorem opposite_shell_disjoint {u v : V} (ht : LocallyTreeAt G u v) :
    Disjoint (shell G u v) (incident G u ∪ starBase G u) := by
  apply Finset.disjoint_left.mpr
  intro z hz hi
  obtain ⟨y,hy,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨hyu,hyv⟩ := Finset.mem_erase.mp hy
  have hvy := (G.mem_neighborFinset _ _).mp hyv
  obtain ⟨hyz,hvz⟩ := Finset.mem_sdiff.mp hz
  have hyz := (mem_incident G y z).mp hyz
  have hvz : v ∉ z.val := fun h => hvz ((mem_incident G v z).mpr h)
  have hnu : u ∉ z.val := by
    intro huz
    have he := (Sym2.mem_and_mem_iff hyu).mp ⟨hyz,huz⟩
    have hyu' : G.Adj y u := G.mem_edgeSet.mp (he ▸ z.2)
    exact ht.1 y hyu'.symm hvy
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hnu ((mem_incident G u z).mp hi)
  · obtain ⟨x,hx,hi⟩ := Finset.mem_biUnion.mp hi
    have hux := (G.mem_neighborFinset _ _).mp hx
    have hxz := (mem_incident G x z).mp (Finset.mem_sdiff.mp hi).1
    by_cases hxy : x = y
    · exact ht.1 y (hxy ▸ hux) hvy
    · have he := (Sym2.mem_and_mem_iff hxy).mp ⟨hxz,hyz⟩
      have hxy' : G.Adj x y := G.mem_edgeSet.mp (he ▸ z.2)
      rcases ht.2 x y hux hxy' hvy.symm with h | h
      · exact hvz (h ▸ hxz)
      · exact hyu h

/-- Lemma 11.4(1) with the manuscript's "only on the opposite side"
hypothesis, for partial colourings and local tree-like geometry. -/
theorem single_shell_cover_opposite {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) {e f : G.edgeSet} {u v x : V}
    (he : e.val = s(u,v)) (hf : f.val = s(u,x)) (heF : e ∉ F)
    (ht : LocallyTreeAt G u v) (hs : φ.Single e (φ.colour f) f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b)
    {c : Colour} (honly : ∀ z, φ.Neighbour e c z → z ∈ shell G u v) :
    ∃ z ∈ shell G u x, z ∈ F ∧ φ.colour z = c := by
  have hdis := opposite_shell_disjoint G ht
  have hc : c ≠ φ.colour f := by
    intro hc
    have hfs := honly f (hc ▸ hs.1)
    exact Finset.disjoint_left.mp hdis hfs
      (Finset.mem_union_left _ ((mem_incident G u f).mpr (hf ▸ Sym2.mem_mk_left u x)))
  obtain ⟨z,hz⟩ := φ.single_saturated_of_no_trivial hs hnt c hc
  have hconf := (mem_conflicts G f z).mpr hz.2.1
  rw [conflicts_star_decomposition G f hf] at hconf
  rcases Finset.mem_union.mp hconf with hi | ho
  · have hze : z ≠ e := fun h => heF (h ▸ hz.1)
    have hinner : z ∈ incident G u ∪ starBase G u := by
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Finset.mem_union_left _ (Finset.mem_erase.mp hi).2
      · exact Finset.mem_union_right _ hi
    have hce : z ∈ conflicts G e := by
      rw [conflicts_star_decomposition G e he]
      apply Finset.mem_union_left
      rcases Finset.mem_union.mp hinner with hi | hi
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hze,hi⟩)
      · exact Finset.mem_union_right _ hi
    exact False.elim (Finset.disjoint_left.mp hdis
      (honly z ⟨hz.1,(mem_conflicts G e z).mp hce,hz.2.2⟩) hinner)
  · exact ⟨z,ho,hz.1,hz.2.2⟩

end Se20Insertion
