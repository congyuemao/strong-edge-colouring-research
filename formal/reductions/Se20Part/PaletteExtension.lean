import Se20Part.PaletteHall

noncomputable section
open scoped Classical
namespace Se20Part

/-- Palette gluing preserves every colour on A. The hypotheses refer to
the fixed ambient graph, so cross-side conflict witnesses are retained. -/
theorem merge_partial_palette {W : Type*} (H : SimpleGraph W)
    (A B : Finset W) (hdis : Disjoint A B)
    (φ : PartialColouring H A) (ψ : PartialColouring H B)
    (p : Colour ≃ Colour)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b → φ.colour a ≠ p (ψ.colour b)) :
    ∃ θ : PartialColouring H (A ∪ B),
      (∀ a ∈ A, θ.colour a = φ.colour a) ∧
      ∀ b ∈ B, θ.colour b = p (ψ.colour b) := by
  let c : W → Colour := fun x => if x ∈ A then φ.colour x else p (ψ.colour x)
  have valid : ∀ a ∈ A ∪ B, ∀ b ∈ A ∪ B, H.Adj a b → c a ≠ c b := by
    intro a ha b hb hab
    by_cases hAa : a ∈ A <;> by_cases hAb : b ∈ A
    · simpa only [c,if_pos hAa,if_pos hAb] using φ.proper hAa hAb hab
    · have hBb := (Finset.mem_union.mp hb).resolve_left hAb
      simpa only [c,if_pos hAa,if_neg hAb] using hcross a hAa b hBb hab
    · have hBa := (Finset.mem_union.mp ha).resolve_left hAa
      simpa only [c,if_neg hAa,if_pos hAb] using (hcross b hAb a hBa hab.symm).symm
    · have hBa := (Finset.mem_union.mp ha).resolve_left hAa
      have hBb := (Finset.mem_union.mp hb).resolve_left hAb
      simpa only [c,if_neg hAa,if_neg hAb] using
        (fun he => ψ.proper hBa hBb hab (p.injective he))
  refine ⟨⟨c,fun _ _ ha hb hab => valid _ ha _ hb hab⟩,?_,?_⟩
  · intro a ha; exact if_pos ha
  · intro b hb
    exact if_neg (fun ha => Finset.disjoint_left.mp hdis ha hb)

/-- G13's nine-core Hall obstruction, generalized to n lists of size at
least n−1. Failure occurs exactly at one common (n−1)-element list. -/
theorem near_full_lists_sdr_or_uniform {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (n : ℕ) (hn : 2 ≤ n) (hI : Fintype.card I = n)
    (hL : ∀ i, n-1 ≤ (L i).card) :
    (∃ f : I → C, Function.Injective f ∧ ∀ i, f i ∈ L i) ∨
      ∃ U : Finset C, U.card = n-1 ∧ ∀ i, L i = U := by
  by_cases hh : ∀ S : Finset I, S.card ≤ (S.biUnion L).card
  · exact Or.inl ((Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hh)
  push_neg at hh
  obtain ⟨S,hS⟩ := hh
  have hSp : 0 < S.card := by omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hSp
  have hsub : L i ⊆ S.biUnion L := fun c hc => Finset.mem_biUnion.mpr ⟨i,hi,hc⟩
  have hlow := (hL i).trans (Finset.card_le_card hsub)
  have hSc : S.card ≤ n := (Finset.card_le_univ _).trans_eq hI
  have heq : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    omega
  have hUc : (S.biUnion L).card = n-1 := by omega
  refine Or.inr ⟨S.biUnion L,hUc,?_⟩
  intro j
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    exact Finset.mem_biUnion.mpr ⟨j,by simp [heq],hc⟩
  · rw [hUc]; exact hL j

/-- G13's three-spoke recolouring pigeonhole: three lists of eight colours
inside a common seventeen-colour pool have a shared colour in two lists. -/
theorem three_eight_lists_overlap {C : Type*} [DecidableEq C]
    (U : Finset C) (L : Fin 3 → Finset C) (hU : U.card ≤ 17)
    (hL : ∀ i, 8 ≤ (L i).card) (hsub : ∀ i, L i ⊆ U) :
    ∃ i j : Fin 3, i ≠ j ∧ ∃ c, c ∈ L i ∧ c ∈ L j := by
  by_contra! hn
  have hdis : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint L := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro c hc hc'
    exact hn i j hij c hc hc'
  have hcard := Finset.card_biUnion hdis
  have hs : (Finset.univ.biUnion L).card ≤ 17 := (Finset.card_le_card
    (show Finset.univ.biUnion L ⊆ U from by
      intro c hc; obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc; exact hsub i hi)).trans hU
  rw [hcard] at hs
  have hsum : 24 ≤ ∑ i : Fin 3, (L i).card := by
    calc
      24 = ∑ _i : Fin 3, 8 := by norm_num
      _ ≤ ∑ i : Fin 3, (L i).card := Finset.sum_le_sum (fun i _ => hL i)
  omega

end Se20Part
