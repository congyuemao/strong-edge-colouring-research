import fourth_pass.SixCases
import fourth_pass.certificates.root_3_3_0
import fourth_pass.certificates.root_4_3_0
import fourth_pass.certificates.root_4_3_4
import fourth_pass.certificates.root_4_3_16
import fourth_pass.certificates.root_4_3_32
import fourth_pass.certificates.root_4_4_0

namespace Se20Fractional.FourthPass
open Finset ThirdPass Packed
attribute [local instance] Classical.propDecidable

theorem no_obstruction14 :
    ∀ H : SimpleGraph (Fin 14), ∀ Q : Finset H.edgeSet, ¬ Obstruction14 H Q :=
  Canonical.no_obstruction_of_six root_3_3_0 root_4_3_0 root_4_3_4
    root_4_3_16 root_4_3_32 root_4_4_0

theorem propositionD_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : PropositionD G :=
  propositionD_of_no_obstruction14 hΔ no_obstruction14

theorem theorem_F_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : FractionalColourable (L2 G) 20 :=
  theorem_F_of_no_obstruction14 hΔ no_obstruction14

#print axioms no_obstruction14
#print axioms propositionD_unconditional
#print axioms theorem_F_unconditional
end Se20Fractional.FourthPass
