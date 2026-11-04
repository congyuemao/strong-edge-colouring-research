import Se20Fractional.DegreeFormula
import Se20Fractional.LocalReed
import Se20Fractional.LocalReedElementary

namespace Se20Fractional
open Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The actual Proposition D, for every clique in the actual square of the line graph. -/
def PropositionD : Prop :=
  ∀ Q : Finset G.edgeSet, Clique (L2 G) Q → 16 ≤ Q.card →
    ∃ y ∈ Q, degreeOn (L2 G) univ y ≤ 19

/-- Theorem F. The only additional assumptions are the explicitly named finite
LP duality statement and Proposition D. -/
theorem theorem_F (hΔ : ∀ v, G.degree v ≤ 4)
    (hLP : FractionalDuality (L2 G)) (hD : PropositionD G) :
    FractionalColourable (L2 G) 20 := by
  have all_subsets (U : Finset G.edgeSet) : FractionalColourableOn (L2 G) U 20 := by
    induction U using Finset.strongInductionOn with
    | _ U ih =>
      by_contra hnot
      have hdelete : ∀ y ∈ U, FractionalColourableOn (L2 G) (U.erase y) 20 := by
        intro y hy
        exact ih (U.erase y) (Finset.erase_ssubset hy)
      have hmin := peeling 20 hnot hdelete
      have hclique : ∀ u ∈ U, ∀ Q : Finset G.edgeSet, Q ⊆ U → u ∈ Q →
          Clique (L2 G) Q → Q.card ≤ 15 := by
        intro u hu Q hQU huQ hQ
        by_contra hlarge
        have h16 : 16 ≤ Q.card := by omega
        obtain ⟨y, hyQ, hydeg⟩ := hD Q hQ h16
        have h20 := hmin y (hQU hyQ)
        have hmono := degreeOn_mono (L2 G) (Finset.subset_univ U) y
        omega
      have hlocal : ∀ y ∈ U, (degreeOn (L2 G) U y : ℝ) + 1 + (15 : ℝ) ≤ 2 * 20 := by
        intro y hy
        have h24 : degreeOn (L2 G) U y ≤ 24 :=
          (degreeOn_mono (L2 G) (Finset.subset_univ U) y).trans (l2_degree_le_24 G hΔ y)
        have hr : (degreeOn (L2 G) U y : ℝ) ≤ 24 := by exact_mod_cast h24
        linarith
      exact hnot (local_fractional_reed (hLP.exists_optimal U) 20 (by norm_num)
        (fun _ => 15) hclique hlocal)
  exact all_subsets univ

#print axioms theorem_F

/-- Theorem F with Proposition D as its only additional hypothesis. The local
fractional Reed bound is supplied by the elementary maximum-stable-set process. -/
theorem theorem_F_of_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : PropositionD G) :
    FractionalColourable (L2 G) 20 := by
  have all_subsets (U : Finset G.edgeSet) : FractionalColourableOn (L2 G) U 20 := by
    induction U using Finset.strongInductionOn with
    | _ U ih =>
      by_contra hnot
      have hdelete : ∀ y ∈ U, FractionalColourableOn (L2 G) (U.erase y) 20 := by
        intro y hy
        exact ih (U.erase y) (Finset.erase_ssubset hy)
      have hmin := peeling 20 hnot hdelete
      have hclique : ∀ u ∈ U, ∀ Q : Finset G.edgeSet, Q ⊆ U → u ∈ Q →
          Clique (L2 G) Q → Q.card ≤ 15 := by
        intro u hu Q hQU huQ hQ
        by_contra hlarge
        have h16 : 16 ≤ Q.card := by omega
        obtain ⟨y, hyQ, hydeg⟩ := hD Q hQ h16
        have h20 := hmin y (hQU hyQ)
        have hmono := degreeOn_mono (L2 G) (Finset.subset_univ U) y
        omega
      have hlocal : ∀ y ∈ U, (degreeOn (L2 G) U y : ℝ) + 1 + (15 : ℝ) ≤ 2*20 := by
        intro y hy
        have h24 : degreeOn (L2 G) U y ≤ 24 :=
          (degreeOn_mono (L2 G) (Finset.subset_univ U) y).trans (l2_degree_le_24 G hΔ y)
        have hr : (degreeOn (L2 G) U y : ℝ) ≤ 24 := by exact_mod_cast h24
        linarith
      exact hnot (local_fractional_reed_elementary (L2 G) U 20 (by norm_num)
        (fun _ => 15) hclique hlocal)
  exact all_subsets univ

#print axioms theorem_F_of_D

end Se20Fractional
