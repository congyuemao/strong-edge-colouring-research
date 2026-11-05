import Se20Part.Definitions

noncomputable section
open scoped Classical
namespace Se20Part

/-- Lemma 3.2, also for overlapping covers and without the unnecessary matching assumption. -/
theorem assembly {V I : Type*} [Fintype I] (G : SimpleGraph V)
    (M : I → Set G.edgeSet) (k : I → ℕ)
    (cover : ∀ e, ∃ i, e ∈ M i)
    (hc : ∀ i, (ConflictGraph G (M i)).Colorable (k i)) :
    StrongColourable G (∑ i, k i) := by
  choose label hlabel using cover
  have valid (i j : I) (e : M i) (f : M j) (hef : (L2 G).Adj e.val f.val) :
      (⟨i, (hc i).some e⟩ : Σ i, Fin (k i)) ≠ ⟨j, (hc j).some f⟩ := by
    intro heq
    obtain ⟨rfl, heq⟩ := Sigma.mk.inj heq
    exact ((hc i).some.valid hef) (eq_of_heq heq)
  let col : (L2 G).Coloring (Σ i, Fin (k i)) := SimpleGraph.Coloring.mk
    (fun e => ⟨label e, (hc (label e)).some ⟨e, hlabel e⟩⟩) (by
      intro e f hef
      exact valid (label e) (label f) ⟨e, hlabel e⟩ ⟨f, hlabel f⟩ hef)
  simpa [StrongColourable, Fintype.card_sigma] using col.colorable

theorem assembly_uniform {V : Type*} (G : SimpleGraph V) (t k : ℕ)
    (M : Fin t → Set G.edgeSet) (cover : ∀ e, ∃ i, e ∈ M i)
    (hc : ∀ i, (ConflictGraph G (M i)).Colorable k) :
    StrongColourable G (t * k) := by
  simpa using assembly G M (fun _ => k) cover hc

/-- The literal chromatic-number inequality of Lemma 3.2 (finite graphs). -/
theorem assembly_chromaticNumber {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (M : I → Set G.edgeSet) (cover : ∀ e, ∃ i, e ∈ M i) :
    (L2 G).chromaticNumber ≤ ∑ i, (ConflictGraph G (M i)).chromaticNumber := by
  have hc := assembly G M (fun i => (ConflictGraph G (M i)).chromaticNumber.toNat)
    cover (fun i => (ConflictGraph G (M i)).colorable_chromaticNumber_of_fintype)
  apply hc.chromaticNumber_le.trans
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum (fun i _ => ENat.natCast_toNat_le_self _)

theorem inducedMatching_colorable_one {V : Type*} {G : SimpleGraph V}
    {M : Set G.edgeSet} (h : IsInducedMatching M) :
    (ConflictGraph G M).Colorable 1 := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
  intro e f hef
  exact (h e.property f.property hef).elim

end Se20Part
