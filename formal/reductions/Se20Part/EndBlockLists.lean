import Se20Part.PaletteExtension
import Se20Part.SmallColourPool

noncomputable section
open scoped Classical
namespace Se20Part

/-- For a complete leaf block, failure after forbidding the fixed boundary
colour forces identical lists even before that colour was removed. -/
theorem clique_leaf_list_failure {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (n : ℕ) (hn : 2 ≤ n) (hi : Fintype.card I = n)
    (hsize : ∀ i, n ≤ (L i).card) (a : C)
    (hbad : ¬ ∃ f : I → C, Function.Injective f ∧ ∀ i, f i ∈ (L i).erase a) :
    ∃ U : Finset C, U.card = n ∧ a ∈ U ∧ ∀ i, L i = U := by
  have hsmall : ∀ i, n-1 ≤ ((L i).erase a).card := by
    intro i
    have hs := hsize i
    by_cases ha : a ∈ L i
    · have he := Finset.card_erase_add_one ha
      omega
    · rw [Finset.erase_eq_of_notMem ha]
      omega
  rcases near_full_lists_sdr_or_uniform (fun i => (L i).erase a) n hn hi hsmall
      with hg | ⟨U,hu,hU⟩
  · exact (hbad hg).elim
  have ha : ∀ i, a ∈ L i := by
    intro i
    by_contra h
    have he := hU i
    rw [Finset.erase_eq_of_notMem h] at he
    have hs := hsize i
    rw [he,hu] at hs
    omega
  have hnot : a ∉ U := by
    have hnI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i⟩ := hnI
    rw [← hU i]
    exact Finset.notMem_erase _ _
  refine ⟨insert a U,?_,Finset.mem_insert_self _ _,?_⟩
  · rw [Finset.card_insert_of_notMem hnot,hu]
    omega
  · intro i
    rw [← hU i,Finset.insert_erase (ha i)]

/-- The two-list end-block repair used by A03. A proper choice of the
non-common colours can avoid one fixed boundary colour by exchanging it
with a common spare colour. This works simultaneously at every boundary
neighbour, without changing any outside colour. -/
theorem two_list_avoid_boundary {I C : Type*} [DecidableEq C]
    (H : SimpleGraph I) (β : I → C) (δ α : C)
    (hδ : ∀ i, β i ≠ δ) (hp : ∀ i j, H.Adj i j → β i ≠ β j) :
    ∃ c : I → C, (∀ i, c i ∈ ({δ,β i} : Finset C)) ∧
      (∀ i, c i ≠ α) ∧ ∀ i j, H.Adj i j → c i ≠ c j := by
  let c : I → C := fun i => if β i = α then δ else β i
  refine ⟨c,?_,?_,?_⟩
  · intro i
    dsimp only [c]
    split_ifs <;> simp
  · intro i
    dsimp only [c]
    split_ifs with hi
    · exact fun he => hδ i (hi.trans he.symm)
    · exact hi
  · intro i j hij
    dsimp only [c]
    split_ifs with hi hj hj
    · exact (hp i j hij (hi.trans hj.symm)).elim
    · exact (hδ j).symm
    · exact hδ i
    · exact hp i j hij

end Se20Part
