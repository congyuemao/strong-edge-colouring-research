import Se20Insertion.TriangleInsertion
import Se20Insertion.Greedy

noncomputable section
open scoped Classical
namespace Se20Insertion

/-- On four vertices, two isolated vertices in a graph guarantee a perfect
matching in its complement. This avoids a case split over the three matchings. -/
theorem complement_matching_of_two_isolated {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hcard : Fintype.card W = 4) (a b : W) (hab : a ≠ b)
    (ha : ∀ x, ¬ H.Adj a x) (hb : ∀ x, ¬ H.Adj b x) :
    ∃ M : Hᶜ.Subgraph, M.IsPerfectMatching := by
  have hc : (Finset.univ \ ({a, b} : Finset W)).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard, Finset.card_pair hab]
  obtain ⟨c, d, hcd, hrest⟩ := Finset.card_eq_two.mp hc
  have hcm : c ∈ Finset.univ \ ({a, b} : Finset W) := by rw [hrest]; simp
  have hdm : d ∈ Finset.univ \ ({a, b} : Finset W) := by rw [hrest]; simp
  have hca : c ≠ a := by
    have hh := (Finset.mem_sdiff.mp hcm).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    exact hh.1
  have hcb : c ≠ b := by
    have hh := (Finset.mem_sdiff.mp hcm).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    exact hh.2
  have hda : d ≠ a := by
    have hh := (Finset.mem_sdiff.mp hdm).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    exact hh.1
  have hdb : d ≠ b := by
    have hh := (Finset.mem_sdiff.mp hdm).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    exact hh.2
  have hall : ∀ x : W, x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    have hx : x ∈ Finset.univ \ ({a, b} : Finset W) := by simp [hxa, hxb]
    rw [hrest] at hx
    exact Or.inr (Or.inr (by simpa using hx))
  let mate (x : W) := if x = a then c else if x = c then a else if x = b then d else b
  have hm : ∀ x, x ≠ mate x ∧ ¬ H.Adj x (mate x) ∧ mate (mate x) = x := by
    intro x
    rcases hall x with hx | hx | hx | hx <;> subst x
    · simp [mate, hca, hca.symm, ha]
    · simp [mate, hab.symm, hcb.symm, hda, hdb, hdb.symm, hcd.symm, hb]
    · simp [mate, hca, hca.symm, show ¬ H.Adj c a from fun h => ha c h.symm]
    · simp [mate, hda, hcd.symm, hdb, hab.symm, hcb.symm,
        show ¬ H.Adj d b from fun h => hb d h.symm]
  let M : Hᶜ.Subgraph := {
    verts := Set.univ
    Adj := fun x y => mate x = y
    adj_sub := by
      intro x y hxy
      subst y
      exact ⟨(hm x).1, (hm x).2.1⟩
    edge_vert := by simp
    symm := ⟨by intro x y hxy; subst y; exact (hm x).2.2⟩ }
  refine ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro x
  exact ⟨mate x, rfl, fun y hy => Eq.symm hy⟩

/-- Lemma 11.37(1): two triangle-free edges at an exceptional vertex coincide. -/
theorem exceptional_triangleFree_incident_unique {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hreg : FourRegular G) (v : V) (hv : ¬ Nonexceptional G v)
    (e f : G.edgeSet) (he : v ∈ e.val) (hf : v ∈ f.val)
    (het : ¬ OnTriangle G e) (hft : ¬ OnTriangle G f) : e = f := by
  obtain ⟨a, hea⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨b, hfb⟩ := Sym2.mem_iff_exists.mp hf
  have hva : G.Adj v a := G.mem_edgeSet.mp (hea ▸ e.2)
  have hvb : G.Adj v b := G.mem_edgeSet.mp (hfb ▸ f.2)
  by_contra hef
  have hab : a ≠ b := by
    intro h; subst b
    exact hef (Subtype.ext (hea.trans hfb.symm))
  let a' : G.neighborSet v := ⟨a, hva⟩
  let b' : G.neighborSet v := ⟨b, hvb⟩
  have hcard : Fintype.card (G.neighborSet v) = 4 := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using hreg v
  apply hv
  apply complement_matching_of_two_isolated (G.induce (G.neighborSet v)) hcard a' b'
    (fun h => hab (congrArg Subtype.val h))
  · intro x hx
    exact het ⟨v, a, x.val, hea, x.2, hx⟩
  · intro x hx
    exact hft ⟨v, b, x.val, hfb, x.2, hx⟩

theorem exceptional_triangleFree_incident_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hreg : FourRegular G) (v : V) (hv : ¬ Nonexceptional G v) :
    ((incident G v).filter (fun e => ¬ OnTriangle G e)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  exact exceptional_triangleFree_incident_unique G hreg v hv e f
    ((mem_incident G _ _).mp (Finset.mem_filter.mp he).1)
    ((mem_incident G _ _).mp (Finset.mem_filter.mp hf).1)
    (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

/-- Lemma 11.37(2). The triangle-free matching is first coloured with seven
colours; all remaining edges are inserted by the verified triangle lemma. -/
theorem strongColourable_of_all_exceptional {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hreg : FourRegular G) (hex : ∀ v, ¬ Nonexceptional G v) :
    StrongColourable G 20 := by
  let M := Finset.univ.filter (fun e : G.edgeSet => ¬ OnTriangle G e)
  let T := Finset.univ.filter (OnTriangle G)
  have hΔ : MaxDegreeFour G := fun v => (hreg v).le
  have hm : ∀ v, ∀ e ∈ M, ∀ f ∈ M, v ∈ e.val → v ∈ f.val → e = f := by
    intro v e he f hf hve hvf
    exact exceptional_triangleFree_incident_unique G hreg v (hex v) e f hve hvf
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
  have hc7 := matching_seven_colourable G hΔ M hm
  have hc20 := SimpleGraph.Colorable.mono (by decide : 7 ≤ 20) hc7
  have hpartial := (partialColouring_iff_colourable (L2 G) M).mpr hc20
  have heq : Finset.univ \ T = M := by ext e; simp [M, T]
  rw [← heq] at hpartial
  obtain ⟨φ⟩ := triangle_edges_last G hΔ Finset.univ T (Finset.subset_univ _)
    (fun e he => (Finset.mem_filter.mp he).2) hpartial
  exact ⟨SimpleGraph.Coloring.mk φ.colour (fun {x y} hxy =>
    φ.proper (Finset.mem_univ _) (Finset.mem_univ _) hxy)⟩

end Se20Insertion
