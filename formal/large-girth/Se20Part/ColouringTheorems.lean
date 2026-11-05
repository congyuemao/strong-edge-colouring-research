import Se20Part.External
import Se20Part.Assembly
import Se20Part.Contraction

noncomputable section
open scoped Classical
namespace Se20Part

/-- Theorem 3.4: only the cited general Kostochka theorem is assumed. -/
theorem theorem_A {V : Type} [Fintype V] (k : Kostochka) {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hc : EdgeColourable G 4) (hg : GirthAtLeast G 41) :
    StrongColourable G 20 := by
  classical
  obtain ⟨c, hm⟩ := hc
  apply assembly_uniform G 4 5 (fun i => {e | c e = i}) (fun e => ⟨c e, rfl⟩)
  intro i
  apply k.to_K6
  · exact matching_maxDegree_six hd (hg.mono (by omega)) (hm i)
  · exact matching_girth (hm i) hg

def PropertyP {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ c : G.edgeSet → Fin 5, (∀ i, IsMatching {e | c e = i}) ∧
    ∀ i (e : {e | c e = i}),
      Nat.card ↥(External G e.val ∩ Covered {e | c e = i}) ≤ 5

def PropertyR {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ c : G.edgeSet → Fin 5, (∀ i, IsMatching {e | c e = i}) ∧
    DegreeLE (ConflictGraph G {e | c e = 3}) 5 ∧ IsInducedMatching {e | c e = 4}

/-- Theorem 3.7. The five matchings and their covered-vertex bounds are precisely Property P. -/
theorem theorem_B_prime {V : Type} [Fintype V] (k : Kostochka) {G : SimpleGraph V}
    (_hd : MaxDegreeFour G) (hg : GirthAtLeast G 69) (hP : PropertyP G) :
    StrongColourable G 20 := by
  classical
  obtain ⟨c, hm, hcov⟩ := hP
  apply assembly_uniform G 5 4 (fun i => {e | c e = i}) (fun e => ⟨c e, rfl⟩)
  intro i
  apply k.to_K5
  · intro e
    exact (matching_degree_eq_covered_external_nat (hg.mono (by omega)) (hm i) e).le.trans
      (hcov i e)
  · exact matching_girth (hm i) hg

/-- Theorem 3.8. Indices 0,1,2,3,4 represent the manuscript's colors 1,2,3,4,5. -/
theorem theorem_B_double_prime {V : Type} [Fintype V] (k : Kostochka)
    {G : SimpleGraph V} (hd : MaxDegreeFour G) (hg : GirthAtLeast G 69)
    (hR : PropertyR G) : StrongColourable G 20 := by
  classical
  obtain ⟨c, hm, hk, hr⟩ := hR
  have h6 (i : Fin 5) : (ConflictGraph G {e | c e = i}).Colorable 5 :=
    k.to_K6 _ _ (matching_maxDegree_six hd (hg.mono (by omega)) (hm i))
      ((matching_girth (hm i) hg).mono (by norm_num))
  have h4 : (ConflictGraph G {e | c e = 3}).Colorable 4 :=
    k.to_K5 _ _ hk (matching_girth (hm 3) hg)
  have h1 := inducedMatching_colorable_one hr
  have h := assembly G (fun i : Fin 5 => {e | c e = i}) ![5, 5, 5, 4, 1]
    (fun e => ⟨c e, rfl⟩) (by
      intro i
      fin_cases i
      · exact h6 0
      · exact h6 1
      · exact h6 2
      · exact h4
      · exact h1)
  simpa [Fin.sum_univ_succ] using h

end Se20Part
