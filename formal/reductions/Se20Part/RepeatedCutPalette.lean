import Se20Part.SmallCutPalette

noncomputable section
open scoped Classical
namespace Se20Part

/-- Four lists of size at least three have representatives if one list has
size at least four. The same bound suffices for fewer than four lists. -/
theorem representatives_three_four {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (hn : Fintype.card I ≤ 4)
    (hL : ∀ i, 3 ≤ (L i).card)
    (hlarge : Fintype.card I = 4 → ∃ i, 4 ≤ (L i).card) :
    ∃ x : I → C, Function.Injective x ∧ ∀ i, x i ∈ L i := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp
  intro J
  rcases J.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · simp
  have hJ := Finset.card_le_univ J
  by_cases hj : J.card ≤ 3
  · exact hj.trans ((hL i).trans (Finset.card_le_card
      (Finset.subset_biUnion_of_mem L hi)))
  · have he : J = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    obtain ⟨j,hj⟩ := hlarge (by omega)
    exact (show J.card ≤ 4 by omega).trans (hj.trans (Finset.card_le_card
      (Finset.subset_biUnion_of_mem L (by simp [he]))))

/-- In the repeated-endpoint case all prescribed source colours can avoid
the whole source boundary. Their rows are then entirely allowed. -/
theorem repeated_cut_small_palette {C : Type*} [Fintype C] [DecidableEq C]
    (hC : Fintype.card C = 20) (n : ℕ) (hn : n ≤ 4)
    (S T L K : Fin n → Finset C)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 3 ≤ (L i).card)
    (hlarge : n = 4 → ∃ i, 4 ≤ (L i).card)
    (hK : ∀ i, n ≤ (K i).card)
    (hdis : ∀ i, Disjoint (L i) (Finset.univ.biUnion S)) :
    ∃ (p : C ≃ C) (x y : Fin n → C),
      Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ p (x i) = y i) ∧
      ∀ c, ¬ starForbidden S T c (p c) := by
  obtain ⟨x,hx,hxL⟩ := representatives_three_four L (by simpa using hn) hL
    (by simpa using hlarge)
  obtain ⟨y,hy,hyK⟩ := representatives_of_card K (by simpa using hK)
  have hxy : ∀ i, ¬ starForbidden S T (x i) (y i) := by
    rintro i ⟨j,hj,_⟩
    exact Finset.disjoint_left.mp (hdis i) (hxL i)
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩)
  have row : ∀ (S T : Fin n → Finset C), (∀ i, (T i).card ≤ 3) →
      ∀ c, (Finset.univ.filter (starForbidden S T c)).card ≤ 3*n := by
    intro S T hT c
    apply (starForbidden_row S T 3 hT c).trans
    calc
      _ ≤ Fintype.card (Fin n) * 3 := Nat.mul_le_mul_right 3 (Finset.card_le_univ _)
      _ = 3*n := by simp only [Fintype.card_fin,Nat.mul_comm]
  obtain ⟨p,hp,hgood⟩ := palette_complete_small hC n hn (starForbidden S T) x y hx hy hxy
    (row S T hT)
    (by
      intro d
      convert row T S hS d using 1
      congr 1
      ext c
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact starForbidden_symm S T c d)
    (by simpa [Nat.mul_comm] using starForbidden_total S T 3 3 hS hT)
  exact ⟨p,x,y,hx,hy,fun i => ⟨hxL i,hyK i,hp i⟩,hgood⟩

end Se20Part
