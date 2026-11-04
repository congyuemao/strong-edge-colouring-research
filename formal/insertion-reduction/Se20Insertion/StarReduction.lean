import Se20Insertion.Suppression
import Se20Insertion.RegularCompletion

noncomputable section
open scoped Classical
namespace Se20Insertion

/-- Proposition 11.38 for the regular finite models. The induction deletes a
vertex, adds a complement matching, and then restricts the resulting colouring.
It never treats a colouring of an edge-deleted graph as a partial colouring. -/
theorem strongColourable_regular_fin_of_starInsertion (h : StarInsertion) :
    ∀ n (G : SimpleGraph (Fin n)), FourRegular G → StrongColourable G 20 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hreg
    by_cases hex : ∀ v, ¬ Nonexceptional G v
    · exact strongColourable_of_all_exceptional G hreg hex
    push_neg at hex
    obtain ⟨v, hv⟩ := hex
    obtain ⟨M, hM⟩ := hv
    let W := {x : Fin n // x ≠ v}
    let S := suppress G v M
    have hS : FourRegular S := by
      intro x
      have hh := suppress_regular G v hreg M hM x
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hh
    let e := (Fintype.equivFin W).symm
    let H := S.comap e
    let i : H ≃g S := SimpleGraph.Iso.comap e S
    have hH : FourRegular H := by
      intro x
      have hd := Nat.card_congr (i.mapNeighborSet x)
      have hr := hS (i x)
      simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd hr ⊢
      exact hd.trans hr
    have hsmall : Fintype.card W < n := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_subtype_lt (p := fun x : Fin n => x ≠ v) (x := v) (by simp))
    have hcH : StrongColourable H 20 := ih (Fintype.card W) hsmall H hH
    have hcS : StrongColourable S 20 := strongColourable_of_iso i.symm hcH
    have hcDelete : StrongColourable (G.induce {x | x ≠ v}) 20 :=
      strongColourable_mono (induce_le_suppress G v M) hcS
    apply fill_star_fin h G hreg v ⟨M, hM⟩ (incident G v)
      (fun e he => (mem_incident G v e).mp he)
    obtain ⟨φ⟩ := starColouring_of_deleteColourable G v hcDelete
    refine ⟨{ colour := φ.colour, proper := ?_ }⟩
    intro x y hx hy hxy
    exact φ.proper (by simpa using hx) (by simpa using hy) hxy

/-- Abstract star insertion reduction, with exactly the restricted states in
Conjecture 11.9*. The regular completion is constructed inside Lean. -/
theorem strongColourable_of_starInsertion (h : StarInsertion) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20 := by
  obtain ⟨n, H, hreg, f, hf⟩ := regularCompletion G hΔ
  obtain ⟨c⟩ := strongColourable_regular_fin_of_starInsertion h n H hreg
  exact ⟨c.comap (L2Map f hf)⟩

theorem strongColourable_of_conj119Star (h : Conj119Star) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20 :=
  strongColourable_of_starInsertion (starInsertion_of_conj119Star h) G hΔ

end Se20Insertion
