import Se20Part.TreeLemma

noncomputable section
open scoped Classical
namespace Se20Part

/-- Candidates retain their problem-edge tag. Different tags for the same
ambient edge are distinct vertices, but do not conflict merely by equality. -/
def taggedConflictGraph {V I : Type*} (G : SimpleGraph V) (P : I → Set G.edgeSet) :
    SimpleGraph (Σ i, P i) where
  Adj x y := x.1 ≠ y.1 ∧ (L2 G).Adj x.2.val y.2.val
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Corrected Haxell remark: the degree bound is on the tagged graph.
Candidate sets themselves may overlap arbitrarily. -/
theorem tagged_haxell_transversal {V I : Type} [Fintype V] [Fintype I]
    (hax : Haxell) (G : SimpleGraph V) (P : I → Set G.edgeSet)
    (hsize : ∀ i, 2 ≤ Nat.card (P i))
    (hdeg : DegreeLE (taggedConflictGraph G P) 1) :
    ∃ f : I → G.edgeSet, (∀ i, f i ∈ P i) ∧ IsInducedMatching (Set.range f) := by
  let W := Σ i, P i
  have hsurj : Function.Surjective (Sigma.fst : W → I) := by
    intro i
    have : Nonempty (P i) := Nat.card_pos_iff.mp (by have := hsize i; omega) |>.1
    exact ⟨⟨i,Classical.choice this⟩,rfl⟩
  have hcard (i : I) : 2 ≤ Fintype.card {w : W // w.1 = i} := by
    let eqv : {w : W // w.1 = i} ≃ P i :=
      { toFun := fun w => w.property ▸ w.val.2
        invFun := fun e => ⟨⟨i,e⟩,rfl⟩
        left_inv := by rintro ⟨⟨j,e⟩,h⟩; dsimp at h; subst j; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr eqv,← Nat.card_eq_fintype_card]
    exact hsize i
  obtain ⟨q,hq,hind⟩ := haxell_degree_one hax (taggedConflictGraph G P)
    Sigma.fst hsurj hdeg hcard
  let f : I → G.edgeSet := fun i => (q i).2.val
  refine ⟨f,?_,?_⟩
  · intro i
    have := (q i).2.property
    exact Eq.mp (congrArg (fun j => (q i).2.val ∈ P j) (hq i)) this
  · rintro e ⟨i,rfl⟩ e' ⟨j,rfl⟩ hadj
    by_cases hij : i = j
    · subst j; exact (L2 G).irrefl hadj
    · exact hind i j hij ⟨by simpa only [hq] using hij,hadj⟩

theorem tagged_haxell_dominating_seed {V : Type} [Fintype V]
    (hax : Haxell) (G : SimpleGraph V) (D M : Set G.edgeSet)
    (P : {h // Problem G D M h} → Set G.edgeSet)
    (hsize : ∀ h, 2 ≤ Nat.card (P h))
    (hdeg : DegreeLE (taggedConflictGraph G P) 1)
    (hvalid : ∀ h e, e ∈ P h → e ∈ M ∧ (L2 G).Adj h.val e ∧
      ∀ r ∈ D, ¬ (L2 G).Adj e r) :
    ∃ J : Set G.edgeSet, J ⊆ M ∧ IsInducedMatching J ∧
      (∀ e ∈ J, ∀ r ∈ D, ¬ (L2 G).Adj e r) ∧
      ∀ h, Problem G D M h → ∃ e ∈ J, (L2 G).Adj h e := by
  obtain ⟨f,hf,hi⟩ := tagged_haxell_transversal hax G P hsize hdeg
  refine ⟨Set.range f,?_,hi,?_,?_⟩
  · rintro e ⟨h,rfl⟩; exact (hvalid h _ (hf h)).1
  · rintro e ⟨h,rfl⟩; exact (hvalid h _ (hf h)).2.2
  · intro h hh
    exact ⟨f ⟨h,hh⟩,⟨⟨h,hh⟩,rfl⟩,(hvalid ⟨h,hh⟩ _ (hf ⟨h,hh⟩)).2.1⟩

end Se20Part
