import third_pass.SupportBound

namespace Se20Fractional.ThirdPass
open Finset DReduction
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Unused slots are isolated; this is the original obstruction on fewer slots. -/
def Obstruction17 (H : SimpleGraph (Fin 17)) (Q : Finset H.edgeSet) : Prop :=
  (∀ v, H.degree v ≤ 4) ∧ Q.card = 16 ∧ Clique (L2 H) Q ∧ LocallyLow H Q ∧
    ∀ v, (∃ u, H.Adj v u) → v ∈ endpoints Q

theorem obstruction17_of_not_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 17), ∃ Q : Finset H.edgeSet, Obstruction17 H Q := by
  obtain ⟨Q,h16,hQ,_,hLow⟩ := obstruction_of_not_D hΔ hD
  have h17 := endpoint_bound_17 hΔ Q hQ (by omega)
  obtain ⟨R,hRcard,hRcl,hRlow,hRΔ,hRcover⟩ := induced_obstruction hΔ Q hQ hLow
  let S := endpoints Q
  let H := G.induce (S : Set V)
  have hc : Fintype.card (S : Set V) ≤ Fintype.card (Fin 17) := by
    change Fintype.card S ≤ Fintype.card (Fin 17)
    rw [Fintype.card_coe, Fintype.card_fin]
    exact h17
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  let j := SimpleGraph.Embedding.map f H
  let T := R.map j.mapEdgeSet
  refine ⟨H.map f, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using degree_map_le_four f hRΔ v
  · change (R.map j.mapEdgeSet).card = 16
    rw [Finset.card_map, hRcard, h16]
  · intro a ha b hb hab
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hb
    exact (l2_embedding_iff j e g).mpr (hRcl e he g hg
      (fun h => hab (congrArg j.mapEdgeSet h)))
  · intro a b hab he
    obtain ⟨x,y,hxy,hxa,hyb⟩ := (H.map_adj f a b).mp hab
    subst a; subst b
    obtain ⟨e,heR,heq⟩ := Finset.mem_map.mp he
    have heq' : e = (⟨s(x,y),hxy⟩ : H.edgeSet) := j.mapEdgeSet.injective heq
    subst e
    rw [local_map f x y]
    exact hRlow x y hxy heR
  · intro v hv
    obtain ⟨w,hvw⟩ := hv
    obtain ⟨x,y,hxy,hxv,hyw⟩ := (H.map_adj f v w).mp hvw
    obtain ⟨e,heR,hxe⟩ := (mem_endpoints R x).mp (hRcover x)
    refine (mem_endpoints T v).mpr ⟨j.mapEdgeSet e, Finset.mem_map.mpr ⟨e,heR,rfl⟩, ?_⟩
    exact Sym2.mem_map.mpr ⟨x,hxe,hxv⟩

/-- The finite premise is still open. -/
theorem propositionD_of_no_obstruction17 (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 17), ∀ Q : Finset H.edgeSet, ¬ Obstruction17 H Q) :
    PropositionD G := by
  by_contra hD
  obtain ⟨H,Q,h⟩ := obstruction17_of_not_D hΔ hD
  exact hfinite H Q h

theorem theorem_F_of_no_obstruction17 (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 17), ∀ Q : Finset H.edgeSet, ¬ Obstruction17 H Q) :
    FractionalColourable (L2 G) 20 :=
  theorem_F_of_D G hΔ (propositionD_of_no_obstruction17 hΔ hfinite)

#print axioms obstruction17_of_not_D
#print axioms propositionD_of_no_obstruction17
#print axioms theorem_F_of_no_obstruction17

end Se20Fractional.ThirdPass
