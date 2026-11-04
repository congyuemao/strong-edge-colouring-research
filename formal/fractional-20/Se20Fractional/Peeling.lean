import Se20Fractional.Definitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Se20Fractional
set_option backward.isDefEq.respectTransparency false
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {U : Finset V}

noncomputable def Colouring.mass (c : Colouring G U) (v : V) : ℝ :=
  ∑ i, if v ∈ c.sets i then c.weight i else 0

theorem Colouring.mass_nonneg (c : Colouring G U) (v : V) : 0 ≤ c.mass v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> simp [c.nonneg]

/-- Split each colour into a copy retaining v and a copy with v removed.
This supplies the exact-cover normalization missing from the informal peeling argument. -/
theorem thin_vertex (c : Colouring G U) (v : V) (hv : v ∈ U) :
    ∃ d : Colouring G U, d.total = c.total ∧ d.mass v = 1 ∧
      ∀ w, w ≠ v → d.mass w = c.mass w := by
  let p : ℝ := 1 / c.mass v
  have hmass : 1 ≤ c.mass v := c.cover v hv
  have hpos : 0 < c.mass v := lt_of_lt_of_le zero_lt_one hmass
  have hp0 : 0 ≤ p := div_nonneg zero_le_one hpos.le
  have hp1 : p ≤ 1 := (div_le_one hpos).mpr hmass
  let ss : Fin (c.n + c.n) → Finset V := Fin.addCases c.sets (fun i => (c.sets i).erase v)
  let xx : Fin (c.n + c.n) → ℝ := Fin.addCases (fun i => p * c.weight i)
    (fun i => (1-p) * c.weight i)
  have hm (w : V) : (∑ i, if w ∈ ss i then xx i else 0) =
      if w = v then p * c.mass v else c.mass w := by
    simp only [ss, xx, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    have h₁ (i : Fin c.n) : (if w ∈ c.sets i then p * c.weight i else 0) =
        p * (if w ∈ c.sets i then c.weight i else 0) := by split_ifs <;> simp
    have h₂ (i : Fin c.n) : (if w ∈ (c.sets i).erase v then (1-p)*c.weight i else 0) =
        if w = v then 0 else (1-p)*(if w ∈ c.sets i then c.weight i else 0) := by
      by_cases h : w = v <;> by_cases h' : w ∈ c.sets i <;> simp [h, h']
    simp_rw [h₁, h₂]
    by_cases h : w = v
    · simp only [h, ite_true, Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
      rfl
    · simp only [h, if_false, ← Finset.mul_sum]
      change p * c.mass w + (1-p)*c.mass w = c.mass w
      ring
  have ht : ∑ i, xx i = c.total := by
    simp only [xx, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, ← Finset.mul_sum]
    unfold Colouring.total
    ring
  have hpv : p * c.mass v = 1 := by exact div_mul_cancel₀ 1 (ne_of_gt hpos)
  let d : Colouring G U := {
    n := c.n+c.n, sets := ss, weight := xx
    nonneg := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [xx, Fin.addCases_left] using mul_nonneg hp0 (c.nonneg i)
      · simpa only [xx, Fin.addCases_right] using mul_nonneg (sub_nonneg.mpr hp1) (c.nonneg i)
    stable := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [ss, Fin.addCases_left] using c.stable i
      · simpa only [ss, Fin.addCases_right] using stable_subset (c.stable i) (Finset.erase_subset v (c.sets i))
    subset := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [ss, Fin.addCases_left] using c.subset i
      · simpa only [ss, Fin.addCases_right] using (Finset.erase_subset v (c.sets i)).trans (c.subset i)
    cover := by
      intro w hw
      rw [hm]
      split_ifs with h
      · rw [hpv]
      · exact c.cover w hw }
  refine ⟨d, ht, ?_, ?_⟩
  · change (∑ i, if v ∈ ss i then xx i else 0) = 1
    rw [hm, if_pos rfl, hpv]
  · intro w hw
    change (∑ i, if w ∈ ss i then xx i else 0) = c.mass w
    rw [hm, if_neg hw]

theorem normalize_colouring (c : Colouring G U) :
    ∃ d : Colouring G U, d.total = c.total ∧ ∀ v ∈ U, d.mass v = 1 := by
  have aux (T : Finset V) (hT : T ⊆ U) :
      ∃ d : Colouring G U, d.total = c.total ∧ ∀ v ∈ T, d.mass v = 1 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨c, rfl, by simp⟩
    | @insert v T hv ih =>
      obtain ⟨d, hd, hm⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hT)
      obtain ⟨e, he, hev, hew⟩ := thin_vertex d v (hT (Finset.mem_insert_self _ _))
      refine ⟨e, he.trans hd, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hev
      · rw [hew w (fun h => hv (h ▸ hw))]
        exact hm w hw
  exact aux U (Finset.Subset.refl _)

theorem pad_colouring (c : Colouring G U) (k : ℝ) (hk : c.total ≤ k) :
    ∃ d : Colouring G U, d.total = k ∧ ∀ v, d.mass v = c.mass v := by
  let d : Colouring G U := {
    n := c.n+1
    sets := Fin.cases ∅ c.sets
    weight := Fin.cases (k-c.total) c.weight
    nonneg := by
      intro i
      refine Fin.cases (sub_nonneg.mpr hk) c.nonneg i
    stable := by
      intro i
      refine Fin.cases (by simp [Stable]) c.stable i
    subset := by
      intro i
      exact Fin.cases (Finset.empty_subset _) c.subset i
    cover := by
      intro v hv
      simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        Finset.notMem_empty, ite_false, zero_add]
      convert c.cover v hv using 1 }
  refine ⟨d, ?_, ?_⟩
  · change (∑ i, Fin.cases (k-c.total) c.weight i) = k
    simp [Fin.sum_univ_succ, Colouring.total]
  · intro v
    simp only [Colouring.mass, d, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      Finset.notMem_empty, ite_false, zero_add]

theorem stable_insert {S : Finset V} {v : V} (hS : Stable G S)
    (hv : ∀ w ∈ S, ¬ G.Adj v w) : Stable G (insert v S) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with haeq | haS
  · subst a
    rcases Finset.mem_insert.mp hb with hbeq | hbS
    · subst b; exact G.irrefl hab
    · exact hv b hbS hab
  · rcases Finset.mem_insert.mp hb with hbeq | hbS
    · subst b; exact hv a haS hab.symm
    · exact hS a haS b hbS hab

/-- Peeling extension at any real budget, including padding and normalization. -/
theorem extend_colouring (v : V) (hv : v ∈ U) (k : ℝ)
    (hcol : FractionalColourableOn G (U.erase v) k)
    (hdegree : (degreeOn G U v : ℝ) + 1 ≤ k) : FractionalColourableOn G U k := by
  obtain ⟨c, hc⟩ := hcol
  obtain ⟨d, hd, hdm⟩ := normalize_colouring c
  obtain ⟨c, hct, hcm⟩ := pad_colouring d k (hd ▸ hc)
  have hexact : ∀ w ∈ U.erase v, c.mass w = 1 := fun w hw => (hcm w).trans (hdm w hw)
  let good (i : Fin c.n) : Prop := ∀ w ∈ c.sets i, ¬ G.Adj v w
  have hnotv (i : Fin c.n) : v ∉ c.sets i := by
    intro h
    exact (Finset.mem_erase.mp (c.subset i h)).1 rfl
  have hbound : (∑ i, if good i then 0 else c.weight i) ≤ (degreeOn G U v : ℝ) := by
    have hi (i : Fin c.n) : (if good i then 0 else c.weight i) ≤
        ∑ w ∈ neighbors G U v, if w ∈ c.sets i then c.weight i else 0 := by
      by_cases hg : good i
      · simp only [hg, ite_true]
        exact Finset.sum_nonneg fun w _ => by split_ifs <;> simp [c.nonneg]
      · simp only [hg, ite_false]
        have hgn : ∃ w ∈ c.sets i, G.Adj v w := by
          simpa only [good, not_forall, not_imp, not_not, exists_prop] using hg
        obtain ⟨w, hw', hadj'⟩ := hgn
        have hN : w ∈ neighbors G U v := (mem_neighbors _ _ _ _).mpr
          ⟨Finset.mem_of_mem_erase (c.subset i hw'), hadj'⟩
        have h := Finset.single_le_sum (f := fun w => if w ∈ c.sets i then c.weight i else 0)
          (fun w _ => by split_ifs <;> simp [c.nonneg]) hN
        simpa [hw'] using h
    calc
      _ ≤ ∑ i, ∑ w ∈ neighbors G U v, if w ∈ c.sets i then c.weight i else 0 :=
        Finset.sum_le_sum fun i _ => hi i
      _ = ∑ w ∈ neighbors G U v, c.mass w := by rw [Finset.sum_comm]; rfl
      _ = ∑ _w ∈ neighbors G U v, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro w hw
        obtain ⟨hwU, hvw⟩ := (mem_neighbors _ _ _ _).mp hw
        exact hexact w (Finset.mem_erase.mpr ⟨hvw.ne.symm, hwU⟩)
      _ = _ := by simp [degreeOn]
  have hgood : 1 ≤ ∑ i, if good i then c.weight i else 0 := by
    have hsplit : (∑ i, if good i then c.weight i else 0) +
        (∑ i, if good i then 0 else c.weight i) = c.total := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    linarith
  let e : Colouring G U := {
    n := c.n
    sets := fun i => if good i then insert v (c.sets i) else c.sets i
    weight := c.weight
    nonneg := c.nonneg
    stable := by
      intro i
      split_ifs with hg
      · exact stable_insert (c.stable i) hg
      · exact c.stable i
    subset := by
      intro i
      split_ifs
      · exact Finset.insert_subset hv ((c.subset i).trans (Finset.erase_subset _ _))
      · exact (c.subset i).trans (Finset.erase_subset _ _)
    cover := by
      intro w hw
      by_cases hwv : w = v
      · subst w
        convert hgood using 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hg : good i <;> simp [hg, hnotv]
      · have hcov := c.cover w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
        convert hcov using 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hg : good i <;> simp [hg, hwv] }
  exact ⟨e, hct.le⟩

/-- Lemma B in the threshold form used in the final theorem. -/
theorem peeling (D : ℕ) (hnot : ¬ FractionalColourableOn G U D)
    (hdelete : ∀ v ∈ U, FractionalColourableOn G (U.erase v) D) :
    ∀ v ∈ U, D ≤ degreeOn G U v := by
  intro v hv
  by_contra h
  have hnat : degreeOn G U v + 1 ≤ D := by omega
  have hreal : (degreeOn G U v : ℝ) + 1 ≤ D := by exact_mod_cast hnat
  exact hnot (extend_colouring v hv D (hdelete v hv) hreal)

#print axioms normalize_colouring
#print axioms extend_colouring
#print axioms peeling

/-- An attained minimum, avoiding any conventions for the infimum of an empty set. -/
def IsFractionalChromaticOn (G : SimpleGraph V) (U : Finset V) (k : ℝ) : Prop :=
  FractionalColourableOn G U k ∧ ∀ r, FractionalColourableOn G U r → k ≤ r

/-- Lemma B for an integer D and an attained vertex-critical fractional optimum. -/
theorem vertex_critical_peeling (D : ℤ) (k : ℝ)
    (hopt : IsFractionalChromaticOn G U k) (hD : (D : ℝ) < k)
    (hcritical : ∀ v ∈ U, ∃ r < k, FractionalColourableOn G (U.erase v) r) :
    ∀ v ∈ U, D ≤ (degreeOn G U v : ℤ) := by
  intro v hv
  by_contra hdeg
  have hnat : (degreeOn G U v : ℤ) + 1 ≤ D := by omega
  have hreal : (degreeOn G U v : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast hnat
  obtain ⟨r, hr, c, hc⟩ := hcritical v hv
  have hsmall : max r (D : ℝ) < k := max_lt hr hD
  have hcol : FractionalColourableOn G (U.erase v) (max r (D : ℝ)) :=
    ⟨c, hc.trans (le_max_left _ _)⟩
  have hext := extend_colouring v hv (max r (D : ℝ)) hcol (hreal.trans (le_max_right _ _))
  exact (not_lt_of_ge (hopt.2 _ hext)) hsmall

#print axioms vertex_critical_peeling

end Se20Fractional
