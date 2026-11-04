import Se20Fractional.Definitions

namespace Se20Fractional
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def endpointRegion (a b : V) : Finset V :=
  (G.neighborFinset a ∪ G.neighborFinset b) \ {a, b}

noncomputable def commonCount (a b : V) : ℕ :=
  (G.neighborFinset a ∩ G.neighborFinset b).card

noncomputable def internalEdges (R : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ R)

noncomputable def touchingEdges (R : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ R)

@[simp] theorem mem_endpointRegion (a b w : V) :
    w ∈ endpointRegion G a b ↔ (G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b := by
  simp [endpointRegion, and_comm, and_left_comm, and_assoc]

theorem degreeOn_univ (v : V) : degreeOn G univ v = G.degree v := by
  unfold degreeOn
  congr 1
  ext w
  simp

/-- The incidence double count, valid for an arbitrary vertex region R. -/
theorem region_degree_sum (R : Finset V) :
    ∑ v ∈ R, G.degree v = (touchingEdges G R).card + (internalEdges G R).card := by
  have hinc (v : V) : G.degree v = ∑ e ∈ G.edgeFinset, if v ∈ e then 1 else 0 := by
    rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
    exact Finset.card_filter _ _
  simp_rw [hinc]
  rw [Finset.sum_comm]
  simp only [touchingEdges, internalEdges, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq]
    have hi : ∀ v, (if v = a ∨ v = b then 1 else 0 : ℕ) =
        (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
      intro v
      by_cases h₁ : v = a <;> by_cases h₂ : v = b <;> simp_all
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;> simp [ha, hb]

/-- The exact endpoint-region size, without the maximum-degree estimate. -/
theorem endpointRegion_card (a b : V) (hab : G.Adj a b) :
    (endpointRegion G a b).card + 2 + commonCount G a b = G.degree a + G.degree b := by
  have hn : ({a, b} : Finset V) ⊆ G.neighborFinset a ∪ G.neighborFinset b := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [hab, hab.symm]
  have hc := Finset.card_sdiff_add_card_eq_card hn
  have hu := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  simp only [Finset.card_pair hab.ne, SimpleGraph.card_neighborFinset_eq_degree] at hc hu
  unfold endpointRegion commonCount
  omega

/-- Characterization of all conflicts using the endpoint region. -/
theorem l2_adj_region (a b : V) (hab : G.Adj a b) (f : G.edgeSet) :
    (L2 G).Adj ⟨s(a,b), hab⟩ f ↔ ∃ w ∈ f.val, w ∈ endpointRegion G a b := by
  rcases f with ⟨f, hf⟩
  induction f using Sym2.ind with
  | _ c d =>
    have hcd : G.Adj c d := hf
    have habn := hab.ne
    have hcdn := hcd.ne
    change ((⟨s(a,b),hab⟩ : G.edgeSet) ≠ ⟨s(c,d),hf⟩ ∧
      ∃ x ∈ s(a,b), ∃ y ∈ s(c,d), x = y ∨ G.Adj x y) ↔
      ∃ w ∈ s(c,d), w ∈ endpointRegion G a b
    constructor
    · rintro ⟨hne, x, hx, y, hy, hxy⟩
      have hne' : ¬ (a = c ∧ b = d ∨ a = d ∧ b = c) := by
        intro h
        exact hne (Subtype.ext (Sym2.eq_iff.mpr h))
      simp only [Sym2.mem_iff] at hx hy
      simp only [Sym2.mem_iff, mem_endpointRegion]
      have hs := hcd.symm
      have ha := hab.symm
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      all_goals grind [SimpleGraph.irrefl]
    · intro h
      constructor
      · intro heq
        have heq' := Sym2.eq_iff.mp (congrArg Subtype.val heq)
        simp only [Sym2.mem_iff, mem_endpointRegion] at h
        grind
      · rcases h with ⟨w, hw, hR⟩
        rcases (mem_endpointRegion G a b w).mp hR with ⟨h, _, _⟩
        rcases h with h | h
        · exact ⟨a, by simp, w, hw, Or.inr h⟩
        · exact ⟨b, by simp, w, hw, Or.inr h⟩

theorem l2_degree_eq_touching (a b : V) (hab : G.Adj a b) :
    degreeOn (L2 G) univ ⟨s(a,b),hab⟩ = (touchingEdges G (endpointRegion G a b)).card := by
  unfold degreeOn
  apply Finset.card_bij (fun f _ => f.val)
  · intro f hf
    simp only [mem_neighbors, mem_univ, true_and] at hf
    exact Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr f.property,
      (l2_adj_region G a b hab f).mp hf⟩
  · intro f hf g hg h
    exact Subtype.ext h
  · intro e he
    obtain ⟨heG, heR⟩ := Finset.mem_filter.mp he
    let f : G.edgeSet := ⟨e, G.mem_edgeFinset.mp heG⟩
    refine ⟨f, ?_, rfl⟩
    simp only [mem_neighbors, mem_univ, true_and]
    exact (l2_adj_region G a b hab f).mpr heR

/-- Lemma C, in subtraction-free form over natural numbers. -/
theorem degree_formula (a b : V) (hab : G.Adj a b) :
    degreeOn (L2 G) univ ⟨s(a,b),hab⟩ + (internalEdges G (endpointRegion G a b)).card =
      ∑ w ∈ endpointRegion G a b, G.degree w := by
  rw [l2_degree_eq_touching]
  exact (region_degree_sum G _).symm

theorem degree_formula_bound (hΔ : ∀ v, G.degree v ≤ 4) (a b : V) (hab : G.Adj a b) :
    degreeOn (L2 G) univ ⟨s(a,b),hab⟩ + 4 * commonCount G a b +
      (internalEdges G (endpointRegion G a b)).card ≤ 24 := by
  have hs : (∑ w ∈ endpointRegion G a b, G.degree w) ≤
      4 * (endpointRegion G a b).card := by
    calc
      _ ≤ ∑ _w ∈ endpointRegion G a b, 4 := Finset.sum_le_sum (fun w _ => hΔ w)
      _ = _ := by simp [Nat.mul_comm]
  have hf := degree_formula G a b hab
  have hr := endpointRegion_card G a b hab
  have ha := hΔ a
  have hb := hΔ b
  omega

theorem l2_degree_le_24 (hΔ : ∀ v, G.degree v ≤ 4) (e : G.edgeSet) :
    degreeOn (L2 G) univ e ≤ 24 := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | _ a b =>
    have h := degree_formula_bound G hΔ a b he
    omega

#print axioms degree_formula
#print axioms degree_formula_bound
#print axioms l2_degree_le_24

end Se20Fractional
