import Se20Part.DegreeTwo
import Se20Part.Transversal

noncomputable section
open scoped Classical
namespace Se20Part

variable {W : Type*} [Fintype W] (H : SimpleGraph W)

/-- A common palette can be reused on fibres between which there are no edges. -/
theorem colourable_of_separated_fibres {C : Type*} (π : W → C) (k : ℕ)
    (hsep : ∀ {x y}, H.Adj x y → π x = π y)
    (hc : ∀ c, (H.induce {x | π x = c}).Colorable k) : H.Colorable k := by
  let cols : ∀ c, (H.induce {x | π x = c}).Coloring (Fin k) := fun c => (hc c).some
  refine ⟨SimpleGraph.Coloring.mk (fun x => cols (π x) ⟨x,rfl⟩) ?_⟩
  intro x y hxy he
  have heq := hsep hxy
  have ht := fibre_value_heq π (fun _ => k) (fun c => cols c) heq x rfl
  apply (cols (π y)).valid (show (H.induce {x | π x = π y}).Adj
    ⟨x,heq⟩ ⟨y,rfl⟩ from hxy)
  exact (eq_of_heq ht).symm.trans he

/-- Residual bipartiteness, including arbitrary extra deletions: meeting every
non-bipartite component of a maximum-degree-two graph suffices. -/
theorem degreeTwo_residual_colourable (hΔ : ∀ x, H.degree x ≤ 2) (D : Set W)
    (hD : ∀ K : H.ConnectedComponent, ¬ K.toSimpleGraph.Colorable 2 →
      ∃ x ∈ K.supp, x ∈ D) : (H.induce Dᶜ).Colorable 2 := by
  apply colourable_of_separated_fibres _
    (fun x : ↥(Dᶜ) => H.connectedComponentMk x.val) 2
  · intro x y hxy
    exact SimpleGraph.ConnectedComponent.sound (show H.Adj x.val y.val from hxy).reachable
  · intro K
    let emb : ((H.induce Dᶜ).induce {x | H.connectedComponentMk x.val = K}) →g
        K.toSimpleGraph := {
      toFun x := ⟨x.val.val, (K.mem_supp_iff _).mpr x.prop⟩
      map_rel' := fun h => h }
    by_cases hk : K.toSimpleGraph.Colorable 2
    · exact ⟨hk.some.comap emb⟩
    obtain ⟨z,hz,hzD⟩ := hD K hk
    let z' : K.supp := ⟨z,hz⟩
    obtain ⟨P⟩ := component_pathCycleOrder H hΔ K
    let emb' : ((H.induce Dᶜ).induce {x | H.connectedComponentMk x.val = K}) →g
        (K.toSimpleGraph.induce {x | x ≠ z'}) := {
      toFun x := ⟨emb x, fun he => x.val.prop ((congrArg Subtype.val he).symm ▸ hzD)⟩
      map_rel' := fun h => h }
    exact ⟨(P.delete_vertex_colourable z').some.comap emb'⟩

namespace Partition
variable {C : Type*} [Fintype C]

theorem monochrome_class_constant (π : W → C) (K : (monochrome H π).ConnectedComponent)
    {x y : W} (hx : x ∈ K.supp) (hy : y ∈ K.supp) : π x = π y := by
  obtain ⟨p⟩ := K.reachable_of_mem_supp hx hy
  induction p with
  | nil => rfl
  | cons h p ih => exact h.2.trans (ih (K.mem_supp_of_adj_mem_supp hx h) hy)

def componentEmbedding (π : W → C) (K : (monochrome H π).ConnectedComponent) :
    K.toSimpleGraph ↪g H where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro x y
    exact ⟨fun h => ⟨h,monochrome_class_constant H π K x.prop y.prop⟩, fun h => h.1⟩

/-- Once a defect set meets each odd component, every original colour class
off the defect set is two-colourable. -/
theorem residual_classes (π : W → C)
    (hΔ : ∀ x, degreeIn H π x (π x) ≤ 2) (D : Set W)
    (hD : ∀ K : (monochrome H π).ConnectedComponent,
      ¬ K.toSimpleGraph.Colorable 2 → ∃ x ∈ K.supp, x ∈ D) :
    ∀ c, (H.induce {x | x ∉ D ∧ π x = c}).Colorable 2 := by
  have hd : ∀ x, (monochrome H π).degree x ≤ 2 := by
    intro x
    have := hΔ x
    rw [← monochrome_degree] at this
    exact_mod_cast this
  obtain ⟨col⟩ := degreeTwo_residual_colourable _ hd D hD
  intro c
  let f : (H.induce {x | x ∉ D ∧ π x = c}) →g ((monochrome H π).induce Dᶜ) := {
    toFun x := ⟨x.val,x.prop.1⟩
    map_rel' := fun {x y} h => ⟨h,x.prop.2.trans y.prop.2.symm⟩ }
  exact ⟨col.comap f⟩

end Partition

def InducedCycle.map {U : Type*} {J : SimpleGraph U} {n : ℕ}
    (C : InducedCycle H n) (f : H ↪g J) : InducedCycle J n where
  vertex i := f (C.vertex i)
  three_le := C.three_le
  injective i hi j hj he := C.injective i hi j hj (f.injective he)
  step i hi := f.toHom.map_adj (C.step i hi)
  close := f.toHom.map_adj C.close
  no_chord i j hij hj hend hadj := C.no_chord i j hij hj hend (f.map_adj_iff.mp hadj)

/-- Proposition 1.1 of NEW_DIRECTIONS, with exactly its partition and
triangle-free-class assumptions and the named Haxell citation. -/
theorem proposition_one_one (hHaxell : Haxell)
    {V : Type} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G)
    (hg : 96 ≤ G.egirth) (π : G.edgeSet → Fin 9)
    (hown : ∀ x, Partition.degreeIn (L2 G) π x (π x) ≤ 2)
    (htri : ∀ x y z, π x = π y → π y = π z →
      (L2 G).Adj x y → (L2 G).Adj y z → ¬ (L2 G).Adj z x) :
    StrongColourable G 19 := by
  let M := Partition.monochrome (L2 G) π
  have hm : ∀ x, M.degree x ≤ 2 := by
    intro x
    have := hown x
    rw [← Partition.monochrome_degree] at this
    exact_mod_cast this
  let I := {K : M.ConnectedComponent // ¬ K.toSimpleGraph.Colorable 2}
  let P (i : I) : PathCycleOrder i.val.toSimpleGraph :=
    (component_pathCycleOrder M hm i.val).some
  have hp (i : I) : (P i).closed ∧ Odd (P i).size :=
    (P i).nonbipartite_closed_odd i.prop
  let C (i : I) : InducedCycle (L2 G) (P i).size :=
    ((P i).inducedCycle (hp i).1).map _ (Partition.componentEmbedding (L2 G) π i.val)
  have hmem (i : I) (x : G.edgeSet) : x ∈ (C i).vertices ↔ x ∈ i.val.supp := by
    letI : DecidableEq G.edgeSet := fun a b => Classical.propDecidable (a = b)
    constructor
    · intro hx
      simp only [InducedCycle.vertices, Finset.mem_image] at hx
      obtain ⟨k,hk,rfl⟩ := hx
      exact ((P i).vertex ⟨k % (P i).size,Nat.mod_lt _ (P i).pos⟩).prop
    · intro hx
      let k := (P i).vertex.symm ⟨x,hx⟩
      rw [InducedCycle.vertices, Finset.mem_image]
      refine ⟨k.val, Finset.mem_range.mpr k.isLt, ?_⟩
      change (((P i).vertex ⟨k.val % (P i).size,_⟩).val) = x
      have he : (⟨k.val % (P i).size,Nat.mod_lt _ (P i).pos⟩ : Fin (P i).size) = k :=
        Fin.ext (Nat.mod_eq_of_lt k.isLt)
      rw [he]
      exact congrArg Subtype.val ((P i).vertex.apply_symm_apply ⟨x,hx⟩)
  have hn (i : I) : 4 ≤ (P i).size := by
    have hthree := (C i).three_le
    by_contra h
    have heq : (P i).size = 3 := by omega
    have hclass (a b : ℕ) : π ((C i).vertex a) = π ((C i).vertex b) :=
      Partition.monochrome_class_constant (L2 G) π i.val
        (((P i).vertex _).prop) (((P i).vertex _).prop)
    apply htri ((C i).vertex 0) ((C i).vertex 1) ((C i).vertex 2)
      (hclass 0 1) (hclass 1 2) ((C i).step 0 (by omega)) ((C i).step 1 (by omega))
    simpa [heq] using (C i).close.symm
  have hdis (i j : I) (hne : i ≠ j) : Disjoint (C i).vertices (C j).vertices := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hne (Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      ((hmem i x).mp hx) ((hmem j x).mp hy)))
  obtain ⟨f,hf,hind⟩ := long_cycles_independent_transversal hHaxell G hΔ hg
    (fun i => (P i).size) C hn hdis
  let D : Set G.edgeSet := Set.range f
  apply nine_classes_one_defect (L2 G) π D
  · rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    by_cases he : i = j
    · subst j; exact (L2 G).irrefl
    · exact hind i j he
  · apply Partition.residual_classes (L2 G) π hown D
    intro K hK
    exact ⟨f ⟨K,hK⟩, (hmem ⟨K,hK⟩ _).mp (hf ⟨K,hK⟩), ⟨⟨K,hK⟩,rfl⟩⟩

end Se20Part
