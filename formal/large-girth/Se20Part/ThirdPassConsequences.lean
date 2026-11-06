import Se20Part.TransferFineEstimate
import Se20Part.TheoremBPlus
import Se20Part.HaxellConsequences

noncomputable section
namespace Se20Part

/-- Intermediate B+ corollary with all numerical and local-lemma assumptions
discharged. `CompletedTheorems.lean` also supplies the embedded-family count. -/
theorem theorem_B_plus_of_counting {V : Type} [Fintype V] (kost : Kostochka)
    (hcount : TransferMatrixSpanningFamilyBound)
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5710) :
    StrongColourable G 20 :=
  theorem_B_plus_of_transfer_bounds kost hcount exp31_transfer_bound G hd hg

end Se20Part
