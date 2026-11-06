import Se20Part.Haxell
import Se20Part.TheoremB
import Se20Part.ConcreteTagged

noncomputable section
namespace Se20Part

/-- Theorem B with the independent-transversal theorem discharged.
The earlier declaration `theorem_B` retains its original type. -/
theorem theorem_B_of_kostochka (kost : Kostochka) {V : Type} [Fintype V]
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 39360) :
    StrongColourable G 20 := theorem_B kost haxell G hd hg

end Se20Part
