import Se20Insertion.PatternGeometry

noncomputable section
open scoped Classical
namespace Se20Insertion.TreePattern

/-- 11.5 with a constructed geometric labelling: no map hypothesis remains. -/
theorem sixty_six_chains_of_girth {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hreg : FourRegular G) (hg : 7 ≤ G.egirth)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F) {e : G.edgeSet}
    (hstop : φ.Stuck e) :
    ∃ P : Finset (Sym2 Colour), 66 ≤ P.card ∧
      ∀ t ∈ P, ∃ a b f g, t = s(a,b) ∧ a ≠ b ∧
        φ.Single e a f ∧ φ.Single e b g ∧ ¬ (L2 G).Adj f g ∧
        φ.SameComponent a b f g := by
  obtain ⟨ι,hι⟩ := exists_geometric_label hreg hg e
  exact sixty_six_chains_of_stuck φ hstop ι hι

end Se20Insertion.TreePattern
