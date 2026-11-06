import Se20Part.DiffuseTriangles

noncomputable section
open scoped Classical
namespace Se20Part
open Partition
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance routeReductionDecEq : DecidableEq G.edgeSet := Classical.decEq _

theorem route_minimum_no_triangles (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π) :
    typedTriangles (L2 G) (fun _ => True) π = ∅ := by
  have hc := no_compact_triangles_ten G hΔ hπ.1.1
  have hd := no_diffuse_triangles_ten G hΔ hg hπ
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles (L2 G) _ _ T).mp hT
  by_cases h : Compact G T
  · have hh := (mem_typedTriangles (L2 G) (Compact G) π T).mpr ⟨ht,h,hcl⟩
    rw [hc] at hh
    exact Finset.notMem_empty _ hh
  · have hh := (mem_typedTriangles (L2 G) (Diffuse G) π T).mpr ⟨ht,h,hcl⟩
    rw [hd] at hh
    exact Finset.notMem_empty _ hh

theorem route_minimum_triangle_free (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π)
    (x y z : G.edgeSet) (hxyc : π x = π y) (hyzc : π y = π z)
    (hxy : (L2 G).Adj x y) (hyz : (L2 G).Adj y z) (hzx : (L2 G).Adj z x) : False := by
  have ht : {x,y,z} ∈ typedTriangles (L2 G) (fun _ => True) π := by
    apply (mem_typedTriangles _ _ _ _).mpr
    refine ⟨by simp [hxy.ne,hyz.ne,hzx.ne.symm],trivial,?_⟩
    intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
    · exact False.elim (hab rfl)
    · exact ⟨hxy,hxyc⟩
    · exact ⟨hzx.symm,hxyc.trans hyzc⟩
    · exact ⟨hxy.symm,hxyc.symm⟩
    · exact False.elim (hab rfl)
    · exact ⟨hyz,hyzc⟩
    · exact ⟨hzx,(hxyc.trans hyzc).symm⟩
    · exact ⟨hyz.symm,hyzc.symm⟩
    · exact False.elim (hab rfl)
  rw [route_minimum_no_triangles G hΔ hg hπ] at ht
  exact Finset.notMem_empty _ ht

/-- Theorem 4.9, with a complete ordering of every remaining odd component.
The unrounded girth conclusion is `g ≤ 2 * size`. -/
theorem routeQ_reduction (hΔ : MaxDegreeFour G) (hg7 : 7 ≤ G.egirth)
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π)
    (K : (monochrome (L2 G) π).ConnectedComponent)
    (hK : ¬ K.toSimpleGraph.Colorable 2) :
    ∃ P : PathCycleOrder K.toSimpleGraph,
      P.closed ∧ Odd P.size ∧ 5 ≤ P.size ∧ g ≤ 2 * P.size := by
  have hd : ∀ e, (monochrome (L2 G) π).degree e ≤ 2 := by
    intro e
    have hh := route_minimum_degree G hΔ hπ.1.1.1.1 e
    rw [← monochrome_degree] at hh
    exact_mod_cast hh
  obtain ⟨P⟩ := component_pathCycleOrder _ hd K
  obtain ⟨hc,ho⟩ := P.nonbipartite_closed_odd hK
  let C : InducedCycle (L2 G) P.size :=
    (P.inducedCycle hc).map _ (componentEmbedding (L2 G) π K)
  have hn : 4 ≤ P.size := by
    have h3 := C.three_le
    by_contra hn
    have heq : P.size = 3 := by omega
    have hclass (a b : ℕ) : π (C.vertex a) = π (C.vertex b) :=
      monochrome_class_constant (L2 G) π K (P.vertex _).prop (P.vertex _).prop
    apply route_minimum_triangle_free G hΔ hg7 hπ (C.vertex 0) (C.vertex 1) (C.vertex 2)
      (hclass 0 1) (hclass 1 2) (C.step 0 (by omega)) (C.step 1 (by omega))
    simpa [heq] using C.close.symm
  refine ⟨P,hc,ho,?_,induced_cycle_length_bound G hg C hn⟩
  obtain ⟨k,hk⟩ := ho
  omega

theorem exists_routeQ_reduction (hΔ : MaxDegreeFour G) (hg7 : 7 ≤ G.egirth)
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    ∃ π : G.edgeSet → Fin 10, RouteMinimum G π ∧
      (∀ e, degreeIn (L2 G) π e (π e) ≤ 2) ∧
      ∀ K : (monochrome (L2 G) π).ConnectedComponent,
        ¬ K.toSimpleGraph.Colorable 2 →
        ∃ P : PathCycleOrder K.toSimpleGraph,
          P.closed ∧ Odd P.size ∧ 5 ≤ P.size ∧ g ≤ 2 * P.size := by
  obtain ⟨π,hπ⟩ := exists_minimumFive (L2 G) (Compact G) (Diffuse G) (Linked G) (C := Fin 10)
  exact ⟨π,hπ,route_minimum_degree G hΔ hπ.1.1.1.1,routeQ_reduction G hΔ hg7 hg hπ⟩

end Se20Part
