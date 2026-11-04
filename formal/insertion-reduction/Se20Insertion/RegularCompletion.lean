import Se20Insertion.GraphBasics

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Two copies, with corresponding deficient vertices joined. -/
def double : SimpleGraph (V × Bool) where
  Adj x y := (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
    (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ G.degree x.1 < 4)
  symm := ⟨by
    rintro x y (⟨hxy, h⟩ | ⟨hxy, hne, hd⟩)
    · exact Or.inl ⟨hxy.symm, h.symm⟩
    · exact Or.inr ⟨hxy.symm, hne.symm, hxy ▸ hd⟩⟩
  loopless := ⟨by
    rintro x (⟨_, h⟩ | ⟨_, h, _⟩)
    · exact G.loopless.irrefl _ h
    · exact h rfl⟩

def doubleInclusion : G →g double G where
  toFun x := (x, false)
  map_rel' := fun h => Or.inl ⟨rfl, h⟩

theorem doubleInclusion_injective : Function.Injective (doubleInclusion G) :=
  fun _ _ h => congrArg Prod.fst h

theorem double_neighbors (x : V × Bool) :
    (double G).neighborFinset x =
      if G.degree x.1 < 4 then
        insert (x.1, !x.2) ((G.neighborFinset x.1).image (fun y => (y, x.2)))
      else (G.neighborFinset x.1).image (fun y => (y, x.2)) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  rcases x with ⟨u, b⟩
  rcases y with ⟨v, c⟩
  cases b <;> cases c <;> by_cases hd : G.degree u < 4 <;>
    simp [double, hd, eq_comm, and_comm]

theorem double_degree (x : V × Bool) :
    (double G).degree x = G.degree x.1 + if G.degree x.1 < 4 then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, double_neighbors]
  have hi : Function.Injective (fun y : V => (y, x.2)) := fun _ _ h => congrArg Prod.fst h
  have hn : (x.1, !x.2) ∉ (G.neighborFinset x.1).image (fun y => (y, x.2)) := by
    rcases x with ⟨u, b⟩
    cases b <;> simp
  by_cases hd : G.degree x.1 < 4
  · simp only [ite_eq_left hd, Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ hi, SimpleGraph.card_neighborFinset_eq_degree]
  · simp only [ite_eq_right hd, Finset.card_image_of_injective _ hi,
      SimpleGraph.card_neighborFinset_eq_degree, Nat.add_zero]

/-- After `d` doublings, a lower bound `degree + d ≥ 4` suffices for a
finite simple 4-regular supergraph. No external graph or conjecture is used. -/
theorem regularCompletion_aux (d : ℕ) :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), MaxDegreeFour G →
      (∀ v, 4 ≤ G.degree v + d) →
      ∃ (n : ℕ) (H : SimpleGraph (Fin n)), FourRegular H ∧
        ∃ f : G →g H, Function.Injective f := by
  induction d with
  | zero =>
    intro V _ G hΔ hlo
    let e := (Fintype.equivFin V).symm
    let H := G.comap e
    let i : H ≃g G := SimpleGraph.Iso.comap e G
    refine ⟨Fintype.card V, H, ?_, i.symm.toHom, i.symm.injective⟩
    intro v
    have hd := Nat.card_congr (i.mapNeighborSet v)
    have hu := hΔ (i v)
    have hl := hlo (i v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd hu hl ⊢
    omega
  | succ d ih =>
    intro V _ G hΔ hlo
    have hdouble : MaxDegreeFour (double G) := by
      intro x
      have hd := double_degree G x
      have hu := hΔ x.1
      simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd hu ⊢
      split_ifs at hd <;> omega
    have hlow : ∀ x, 4 ≤ (double G).degree x + d := by
      intro x
      have hd := double_degree G x
      have hu := hΔ x.1
      have hl := hlo x.1
      simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd hu hl ⊢
      split_ifs at hd <;> omega
    obtain ⟨n, H, hr, f, hf⟩ := ih (double G) hdouble hlow
    exact ⟨n, H, hr, f.comp (doubleInclusion G), hf.comp (doubleInclusion_injective G)⟩

theorem regularCompletion (hΔ : MaxDegreeFour G) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), FourRegular H ∧
      ∃ f : G →g H, Function.Injective f :=
  regularCompletion_aux 4 G hΔ (fun _ => by omega)

end Se20Insertion
