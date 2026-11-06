import Se20Part.ExternalStars

noncomputable section
open scoped Classical
namespace Se20Part

/-- The actual nine internal lists in G13 have only one failure state.
Equality forces all six spoke colours, three colours at every external
star, disjointness of the three contributions, and identical stars on
each side. -/
theorem k33_palette_failure (R : Finset Colour) (A B : Fin 3 → Finset Colour)
    (hR : R.card ≤ 6) (hA : ∀ i, (A i).card ≤ 3) (hB : ∀ j, (B j).card ≤ 3)
    (hfail : ¬ ∃ c : Fin 3 × Fin 3 → Colour, Function.Injective c ∧
      ∀ p, c p ∈ Finset.univ \ (R ∪ A p.1 ∪ B p.2)) :
    R.card = 6 ∧
      (∀ i, (A i).card = 3 ∧ A i = A 0) ∧
      (∀ j, (B j).card = 3 ∧ B j = B 0) ∧
      Disjoint R (A 0) ∧ Disjoint (R ∪ A 0) (B 0) := by
  let L := fun p : Fin 3 × Fin 3 => Finset.univ \ (R ∪ A p.1 ∪ B p.2)
  have hL : ∀ p, 9-1 ≤ (L p).card := by
    intro p
    have hu := Finset.card_union_le (R ∪ A p.1) (B p.2)
    have hv := Finset.card_union_le R (A p.1)
    have ha := hA p.1
    have hb := hB p.2
    have he := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour)
      (R ∪ A p.1 ∪ B p.2)
    simp only [Finset.univ_inter,Finset.card_univ,Fintype.card_fin] at he
    change (L p).card + _ = 20 at he
    omega
  obtain h | ⟨U,hU,hLU⟩ := near_full_lists_sdr_or_uniform L 9 (by decide) (by decide) hL
  · exact False.elim (hfail h)
  let D := Finset.univ \ U
  have hDc : D.card = 12 := by
    simp only [D,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    omega
  have hD : ∀ i j, R ∪ A i ∪ B j = D := by
    intro i j
    have he := congrArg (fun S : Finset Colour => Finset.univ \ S) (hLU (i,j))
    have hcomp : ∀ T : Finset Colour, Finset.univ \ (Finset.univ \ T) = T := by
      intro T; ext c; simp
    simpa only [L,hcomp] using he
  have tight : ∀ i j, R.card = 6 ∧ (A i).card = 3 ∧ (B j).card = 3 ∧
      Disjoint R (A i) ∧ Disjoint (R ∪ A i) (B j) := by
    intro i j
    have hu := Finset.card_union_add_card_inter (R ∪ A i) (B j)
    have hv := Finset.card_union_add_card_inter R (A i)
    rw [hD i j,hDc] at hu
    have ha := hA i
    have hb := hB j
    have hRA := Finset.card_union_le R (A i)
    refine ⟨by omega,by omega,by omega,?_,?_⟩
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      exact Finset.card_eq_zero.mp (by omega)
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      exact Finset.card_eq_zero.mp (by omega)
  have hAe : ∀ i, A i = A 0 := by
    intro i
    have hi := tight i 0
    have hz := tight 0 0
    have hiD := hD i 0
    have hzD := hD 0 0
    ext c
    have hai : c ∈ A i → c ∉ R := fun h hc => Finset.disjoint_left.mp hi.2.2.2.1 hc h
    have haz : c ∈ A 0 → c ∉ R := fun h hc => Finset.disjoint_left.mp hz.2.2.2.1 hc h
    have hbi : c ∈ A i → c ∉ B 0 := fun h hc =>
      Finset.disjoint_left.mp hi.2.2.2.2 (Finset.mem_union_right _ h) hc
    have hbz : c ∈ A 0 → c ∉ B 0 := fun h hc =>
      Finset.disjoint_left.mp hz.2.2.2.2 (Finset.mem_union_right _ h) hc
    have he : (c ∈ R ∨ c ∈ A i) ∨ c ∈ B 0 ↔ (c ∈ R ∨ c ∈ A 0) ∨ c ∈ B 0 := by
      simpa only [Finset.mem_union] using
        (show c ∈ R ∪ A i ∪ B 0 ↔ c ∈ R ∪ A 0 ∪ B 0 by rw [hiD,hzD])
    tauto
  have hBe : ∀ j, B j = B 0 := by
    intro j
    have hi := tight 0 j
    have hz := tight 0 0
    have hiD := hD 0 j
    have hzD := hD 0 0
    ext c
    have hbi : c ∈ B j → c ∉ R ∪ A 0 := fun h hc => Finset.disjoint_left.mp hi.2.2.2.2 hc h
    have hbz : c ∈ B 0 → c ∉ R ∪ A 0 := fun h hc => Finset.disjoint_left.mp hz.2.2.2.2 hc h
    have he : c ∈ R ∪ A 0 ∨ c ∈ B j ↔ c ∈ R ∪ A 0 ∨ c ∈ B 0 := by
      simpa only [Finset.mem_union] using
        (show c ∈ R ∪ A 0 ∪ B j ↔ c ∈ R ∪ A 0 ∪ B 0 by rw [hiD,hzD])
    tauto
  exact ⟨(tight 0 0).1,fun i => ⟨(tight i 0).2.1,hAe i⟩,
    fun j => ⟨(tight 0 j).2.2.1,hBe j⟩,(tight 0 0).2.2.2⟩

end Se20Part
