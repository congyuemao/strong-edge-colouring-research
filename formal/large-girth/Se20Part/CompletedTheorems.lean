import Se20Part.EmbeddedFamilyBound
import Se20Part.ThirdPassConsequences

noncomputable section
namespace Se20Part

/-- Theorem B+ with only the explicitly retained Kostochka literature theorem.
The original parameterized theorem is preserved without changing its statement. -/
theorem theorem_B_plus_of_kostochka {V : Type} [Fintype V] (kost : Kostochka)
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5710) :
    StrongColourable G 20 :=
  theorem_B_plus_of_counting kost transfer_spanning_family_bound G hd hg

/-- The unchanged first-pass specification, now inhabited. -/
theorem theorem_B_plus_statement : TheoremBPlusStatement := by
  intro kost _lll V _ G hd hg
  exact theorem_B_plus_of_kostochka kost G hd hg

end Se20Part
