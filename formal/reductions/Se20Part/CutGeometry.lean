import Se20Part.ConflictBounds

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance cutGeometryDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Actual ambient edges with both endpoints on a specified side. -/
def sideEdges (A : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ A)

@[simp] theorem mem_sideEdges (A : Finset V) (e : G.edgeSet) :
    e ∈ sideEdges G A ↔ ∀ v ∈ e.val, v ∈ A := by simp [sideEdges]

def sideStar (A : Finset V) (v : V) : Finset G.edgeSet := incident G v ∩ sideEdges G A

def sideNear (A : Finset V) (v : V) : Finset G.edgeSet :=
  (sideEdges G A).filter (fun e => ∃ w ∈ e.val, w = v ∨ G.Adj v w)

theorem sideStar_card (A : Finset V) {v : V} (hv : v ∈ A) :
    (sideStar G A v).card = (G.neighborFinset v ∩ A).card := by
  let f : {w : V // w ∈ G.neighborFinset v ∩ A} → G.edgeSet :=
    fun w => ⟨s(v,w.val),G.mem_edgeSet.mpr ((G.mem_neighborFinset _ _).mp
      (Finset.mem_inter.mp w.prop).1)⟩
  have hf : Function.Injective f := by
    intro w z he
    have hh : s(v,w.val) = s(v,z.val) := congrArg Subtype.val he
    exact Subtype.ext (Sym2.eq_iff.mp hh |>.elim (fun h => h.2)
      (fun h => h.2.trans h.1))
  have he : Finset.univ.image f = sideStar G A v := by
    ext e
    constructor
    · rintro he
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp he
      refine Finset.mem_inter.mpr ⟨by simp [f],?_⟩
      apply (mem_sideEdges G _ _).mpr
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hv
      · exact (Finset.mem_inter.mp w.prop).2
    · intro he
      obtain ⟨hve,hea⟩ := Finset.mem_inter.mp he
      obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp ((mem_incident G v e).mp hve)
      have hvw : G.Adj v w := G.mem_edgeSet.mp (hew ▸ e.prop)
      have hwA : w ∈ A := (mem_sideEdges G _ _).mp hea w (hew ▸ Sym2.mem_mk_right v w)
      exact Finset.mem_image.mpr ⟨⟨w,Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset v w).mpr hvw,hwA⟩⟩,Finset.mem_univ _,Subtype.ext hew.symm⟩
  rw [← he,Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_coe]

/-- A near-edge set is covered by full stars at the side-neighbours; the
edge incident with the boundary vertex is counted via its other endpoint. -/
theorem sideNear_subset (A : Finset V) (v : V) :
    sideNear G A v ⊆ (G.neighborFinset v ∩ A).biUnion (incident G) := by
  intro e he
  obtain ⟨heA,w,hw,hwv⟩ := Finset.mem_filter.mp he
  rcases hwv with rfl | hvw
  · obtain ⟨u,heu⟩ := Sym2.mem_iff_exists.mp hw
    have hvu : G.Adj w u := G.mem_edgeSet.mp (heu ▸ e.prop)
    have hu : u ∈ e.val := heu ▸ Sym2.mem_mk_right w u
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hvu,(mem_sideEdges G _ _).mp heA u hu⟩,
      (mem_incident G _ _).mpr hu⟩
  · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hvw,(mem_sideEdges G _ _).mp heA w hw⟩,
      (mem_incident G _ _).mpr hw⟩

theorem sideNear_card (hΔ : MaxDegreeFour G) (A : Finset V) (v : V) :
    (sideNear G A v).card ≤ (G.neighborFinset v ∩ A).card * 4 := by
  calc
    _ ≤ ((G.neighborFinset v ∩ A).biUnion (incident G)).card :=
      Finset.card_le_card (sideNear_subset G A v)
    _ ≤ ∑ w ∈ G.neighborFinset v ∩ A, (incident G w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ G.neighborFinset v ∩ A, 4 :=
      Finset.sum_le_sum (fun w _ => by simpa only [card_incident] using hΔ w)
    _ = _ := by simp

theorem sideStar_subset_near (A : Finset V) (v : V) :
    sideStar G A v ⊆ sideNear G A v := by
  intro e he
  obtain ⟨hv,heA⟩ := Finset.mem_inter.mp he
  exact Finset.mem_filter.mpr ⟨heA,v,(mem_incident G _ _).mp hv,Or.inl rfl⟩

/-- Boundary multiplicity reduces both local budgets, including repeated
endpoints in three- and four-edge cuts. -/
theorem cut_endpoint_budgets (hΔ : MaxDegreeFour G) (A : Finset V)
    {v : V} (hv : v ∈ A) (B : Finset V)
    (hB : B ⊆ G.neighborFinset v) (hBA : Disjoint B A) :
    (sideStar G A v).card + B.card ≤ 4 ∧
    (sideNear G A v).card ≤ (4 - B.card) * 4 := by
  have hdis : Disjoint (G.neighborFinset v ∩ A) B :=
    hBA.symm.mono_left Finset.inter_subset_right
  have hsub : (G.neighborFinset v ∩ A) ∪ B ⊆ G.neighborFinset v :=
    Finset.union_subset Finset.inter_subset_left hB
  have hcount := (Finset.card_le_card hsub).trans (show (G.neighborFinset v).card ≤ 4 by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hΔ v)
  rw [Finset.card_union_of_disjoint hdis] at hcount
  refine ⟨by rwa [sideStar_card G A hv],?_⟩
  exact (sideNear_card G hΔ A v).trans (Nat.mul_le_mul_right 4 (by omega))

/-- The exact cross-side conflict relation: only a crossing edge joining
two endpoints can witness it. Equality of endpoints is excluded by the cut. -/
theorem cut_cross_conflict_iff (A : Finset V) {e f : G.edgeSet}
    (he : e ∈ sideEdges G A) (hf : f ∈ sideEdges G (Finset.univ \ A)) :
    (L2 G).Adj e f ↔ ∃ u ∈ e.val, ∃ v ∈ f.val, G.Adj u v := by
  constructor
  · rintro ⟨_,u,hu,v,hv,huv⟩
    refine ⟨u,hu,v,hv,?_⟩
    rcases huv with rfl | huv
    · exact False.elim ((Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp hf u hv)).2
        ((mem_sideEdges G _ _).mp he u hu))
    · exact huv
  · rintro ⟨u,hu,v,hv,huv⟩
    refine ⟨?_,u,hu,v,hv,Or.inr huv⟩
    intro hef
    subst f
    exact (Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp hf u hu)).2
      ((mem_sideEdges G _ _).mp he u hu)

/-- Proper strong colours on a star are all distinct. This avoids losing
the subtraction of the own-star size in repeated-endpoint cuts. -/
theorem sideStar_colour_card (A : Finset V)
    (φ : PartialColouring (L2 G) (sideEdges G A)) (v : V) :
    ((sideStar G A v).image φ.colour).card = (sideStar G A v).card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf heq
  by_contra hne
  exact φ.proper (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hf).2
    ⟨hne,v,(mem_incident G _ _).mp (Finset.mem_inter.mp he).1,
      v,(mem_incident G _ _).mp (Finset.mem_inter.mp hf).1,Or.inl rfl⟩ heq

/-- The source-forbidden union has size at most 3d+u, not 4d+u:
the d colours on the own star were counted in both terms. -/
theorem sideNear_union_colour_budget (hΔ : MaxDegreeFour G) (A : Finset V)
    (φ : PartialColouring (L2 G) (sideEdges G A)) {v : V} (hv : v ∈ A)
    (U : Finset Colour) (hU : (sideStar G A v).image φ.colour ⊆ U) :
    (((sideNear G A v).image φ.colour) ∪ U).card ≤
      3 * (G.neighborFinset v ∩ A).card + U.card := by
  let N := (sideNear G A v).image φ.colour
  have hN : N.card ≤ (G.neighborFinset v ∩ A).card * 4 :=
    Finset.card_image_le.trans (sideNear_card G hΔ A v)
  have hsub : (sideStar G A v).image φ.colour ⊆ N ∩ U := by
    intro c hc
    refine Finset.mem_inter.mpr ⟨?_,hU hc⟩
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨e,sideStar_subset_near G A v he,rfl⟩
  have hI := Finset.card_le_card hsub
  rw [sideStar_colour_card G A φ v,sideStar_card G A hv] at hI
  have he := Finset.card_union_add_card_inter N U
  change (N ∪ U).card ≤ _
  omega

/-- Budget for all distinct boundary endpoints on one side. Counting
distinct vertices is essential when several cut edges share an endpoint. -/
theorem boundary_star_colour_budget (hΔ : MaxDegreeFour G) (A P : Finset V)
    (hP : P ⊆ A) (φ : PartialColouring (L2 G) (sideEdges G A)) :
    (P.biUnion (fun v => (sideStar G A v).image φ.colour)).card +
      (∑ v ∈ P, (G.neighborFinset v \ A).card) ≤ 4 * P.card := by
  have hlocal : ∀ v ∈ P, (sideStar G A v).card + (G.neighborFinset v \ A).card ≤ 4 := by
    intro v hv
    rw [sideStar_card G A (hP hv)]
    have he := Finset.card_sdiff_add_card_inter (G.neighborFinset v) A
    rw [SimpleGraph.card_neighborFinset_eq_degree] at he
    have := hΔ v
    omega
  calc
    _ ≤ (∑ v ∈ P, (sideStar G A v).card) +
        (∑ v ∈ P, (G.neighborFinset v \ A).card) := by
      apply Nat.add_le_add_right
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum
        (fun v _ => Finset.card_image_le))
    _ = ∑ v ∈ P, ((sideStar G A v).card + (G.neighborFinset v \ A).card) :=
      (Finset.sum_add_distrib).symm
    _ ≤ ∑ _v ∈ P, 4 := Finset.sum_le_sum hlocal
    _ = _ := by simp [Nat.mul_comm]

end Se20Part
