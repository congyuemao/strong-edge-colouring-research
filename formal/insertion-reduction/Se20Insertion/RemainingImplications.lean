import Se20Insertion.StarReduction
import Se20Insertion.Fragmentation

noncomputable section
open scoped Classical
namespace Se20Insertion

/-- The unrestricted extension hypothesis in 11.35. As for StarInsertion,
the conclusion records the resulting colouring, not a history of swaps. -/
def UnrestrictedStarInsertion : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ v (U : Finset G.edgeSet), StarSet G v U →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U),
        ∃ e ∈ U, Nonempty (PartialColouring (L2 G) (insert e (Finset.univ \ U)))

theorem strongColourable_of_unrestricted_star (h : UnrestrictedStarInsertion)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hd : MaxDegreeFour G) :
    StrongColourable G 20 := by
  apply strongColourable_of_starInsertion _ G hd
  intro n J hj v _ U hU _ φ
  exact h n J (fun x => (hj x).le) v U hU φ

def Conj1126Strong : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ (F : Finset G.edgeSet) (h : G.edgeSet), h ∈ F →
      ∀ φ : PartialColouring (L2 G) (F.erase h), φ.LocallyMaximal → ∃ a, φ.Free h a

theorem conj1126Weak_of_strong (h : Conj1126Strong) : Conj1126Weak := by
  intro n G hd F e he φ hm
  exact Or.inl (h n G hd F e he φ hm)

theorem strongColourable_of_conj1126Strong (h : Conj1126Strong)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hd : MaxDegreeFour G) :
    StrongColourable G 20 := strongColourable_of_conj1126 (conj1126Weak_of_strong h) G hd

end Se20Insertion
