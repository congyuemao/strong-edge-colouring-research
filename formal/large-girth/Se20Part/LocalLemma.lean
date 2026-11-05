import Se20Part.External

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part

theorem eventProb_nonneg {Ω : Type} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (S : Set Ω) : 0 ≤ eventProb p S := by
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact hp ω
  · exact le_rfl

theorem eventProb_mono {Ω : Type} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) {S T : Set Ω} (h : S ⊆ T) : eventProb p S ≤ eventProb p T := by
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hs : ω ∈ S
  · simp [hs,h hs]
  · by_cases ht : ω ∈ T <;> simp [hs,ht,hp ω]

theorem avoid_antitone {Ω I : Type} (E : I → Set Ω) {S T : Finset I} (h : S ⊆ T) :
    Avoid E T ⊆ Avoid E S := fun _ hω i hi => hω i (h hi)

theorem avoid_insert_probability {Ω I : Type} [Fintype Ω] (p : Ω → ℝ)
    (E : I → Set Ω) (S : Finset I) (i : I) :
    eventProb p (Avoid E (insert i S)) =
      eventProb p (Avoid E S) - eventProb p (E i ∩ Avoid E S) := by
  unfold eventProb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  have hi : ω ∈ Avoid E (insert i S) ↔ ω ∉ E i ∧ ω ∈ Avoid E S := by simp [Avoid]
  by_cases hs : ω ∈ Avoid E S <;> by_cases he : ω ∈ E i <;> simp [hi,hs,he]

/-- Multiplicative lower bound from conditional bounds on proper partial sets.
No division by the probability of an avoidance event is needed. -/
theorem avoid_product_lower {Ω I : Type} [Fintype Ω] (p : Ω → ℝ) (E : I → Set Ω)
    (x : I → ℝ) (hx : ∀ i, x i < 1) (T A : Finset I)
    (hcond : ∀ i ∈ A, ∀ R ⊆ A, i ∉ R →
      eventProb p (E i ∩ Avoid E (T ∪ R)) ≤ x i * eventProb p (Avoid E (T ∪ R))) :
    eventProb p (Avoid E T) * ∏ i ∈ A, (1-x i) ≤ eventProb p (Avoid E (T ∪ A)) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hprev := ih (fun j hj R hR hjR => hcond j (Finset.mem_insert_of_mem hj) R
      (hR.trans (Finset.subset_insert _ _)) hjR)
    have hnext := hcond i (by simp) A (Finset.subset_insert _ _) hi
    rw [Finset.union_insert,avoid_insert_probability,Finset.prod_insert hi]
    have hmul := mul_le_mul_of_nonneg_left hprev (by linarith [hx i] : 0 ≤ 1-x i)
    nlinarith

theorem local_lemma_conditional {Ω I : Type} [Fintype Ω] [Fintype I]
    (p : Ω → ℝ) (E : I → Set Ω) (D : SimpleGraph I) (x : I → ℝ)
    (hp : ∀ ω, 0 ≤ p ω)
    (hind : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ D.Adj i j) →
      eventProb p (E i ∩ Avoid E S) = eventProb p (E i) * eventProb p (Avoid E S))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hevent : ∀ i, eventProb p (E i) ≤ x i * ∏ j ∈ D.neighborFinset i, (1-x j)) :
    ∀ S : Finset I, ∀ i ∉ S,
      eventProb p (E i ∩ Avoid E S) ≤ x i * eventProb p (Avoid E S) := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih
  intro i hi
  let A := S.filter (D.Adj i)
  let T := S.filter (fun j => ¬ D.Adj i j)
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hunion : T ∪ A = S := by ext j; simp [A,T]; tauto
  have hT (j : I) (hj : j ∈ T) : ¬ D.Adj i j := (Finset.mem_filter.mp hj).2
  have hA (j : I) (hj : j ∈ A) : D.Adj i j := (Finset.mem_filter.mp hj).2
  have hlower : eventProb p (Avoid E T) * ∏ j ∈ A, (1-x j) ≤ eventProb p (Avoid E S) := by
    rw [← hunion]
    apply avoid_product_lower p E x (fun j => (hx j).2)
    intro j hj R hR hjR
    have hjT : j ∉ T := fun hh => hT j hh (hA j hj)
    have hjU : j ∉ T ∪ R := by simp [hjT,hjR]
    have hsub : T ∪ R ⊆ S := Finset.union_subset hTS (hR.trans hAS)
    have hstrict : T ∪ R ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun hh => hjU (hh ▸ hAS hj)⟩
    exact ih (T ∪ R) hstrict j hjU
  have hprob : eventProb p (E i ∩ Avoid E S) ≤ eventProb p (E i) * eventProb p (Avoid E T) := by
    rw [← hind i T (fun h => hi (hTS h)) hT]
    exact eventProb_mono hp (fun _ h => ⟨h.1,avoid_antitone E hTS h.2⟩)
  have hsubset : A ⊆ D.neighborFinset i := by intro j hj; simpa using hA j hj
  have hprod : (∏ j ∈ D.neighborFinset i, (1-x j)) ≤ ∏ j ∈ A, (1-x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ hsubset
    · intro j hj; linarith [(hx j).2]
    · intro j hj hjA; linarith [(hx j).1]
  calc
    eventProb p (E i ∩ Avoid E S) ≤ eventProb p (E i) * eventProb p (Avoid E T) := hprob
    _ ≤ (x i * ∏ j ∈ A, (1-x j)) * eventProb p (Avoid E T) :=
      mul_le_mul_of_nonneg_right ((hevent i).trans (mul_le_mul_of_nonneg_left hprod (hx i).1))
        (eventProb_nonneg hp _)
    _ = x i * (eventProb p (Avoid E T) * ∏ j ∈ A, (1-x j)) := by ring
    _ ≤ x i * eventProb p (Avoid E S) := mul_le_mul_of_nonneg_left hlower (hx i).1

/-- The general asymmetric finite Lovász local lemma, with joint independence
from every collection of non-neighbor event complements. -/
theorem lovasz_local_lemma : LovaszLocalLemma := by
  intro Ω I _ _ p E D x hp hsum hind hx hevent
  have hcond := local_lemma_conditional p E D x hp hind hx hevent
  have hlower := avoid_product_lower p E x (fun i => (hx i).2) ∅ Finset.univ
    (fun i hi R hR hiR => by simpa using hcond R i hiR)
  have hempty : eventProb p (Avoid E ∅) = 1 := by simp [eventProb,Avoid,hsum]
  rw [hempty,one_mul,Finset.empty_union] at hlower
  exact lt_of_lt_of_le (Finset.prod_pos (fun i _ => by linarith [(hx i).2])) hlower

end Se20Part
