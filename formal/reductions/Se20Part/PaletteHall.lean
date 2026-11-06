import Se20Part.Definitions
import Mathlib.Combinatorics.Hall.Finite

noncomputable section
open scoped Classical
namespace Se20Part
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Hall's theorem formulated as the absence of a forbidden rectangle whose
row and column sizes sum to more than the palette size. -/
theorem palette_equiv_of_no_rectangle (R : A → B → Prop)
    (hcard : Fintype.card A = Fintype.card B)
    (hrect : ∀ S : Finset A, ∀ T : Finset B,
      Fintype.card B < S.card + T.card → ∃ x ∈ S, ∃ y ∈ T, ¬ R x y) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  let L : A → Finset B := fun x => Finset.univ.filter (fun y => ¬ R x y)
  have hh : ∀ S : Finset A, S.card ≤ (S.biUnion L).card := by
    intro S
    by_contra hn
    let T := Finset.univ \ S.biUnion L
    have hc : T.card = Fintype.card B - (S.biUnion L).card := by
      simp only [T,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hu : (S.biUnion L).card ≤ Fintype.card B := Finset.card_le_univ _
    obtain ⟨x,hx,y,hy,hxy⟩ := hrect S T (by omega)
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_biUnion.mpr
      ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩⟩)
  obtain ⟨f,hf,hfL⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hh
  have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩
  exact ⟨Equiv.ofBijective f hbij,fun x => (Finset.mem_filter.mp (hfL x)).2⟩

/-- Row, column, and total forbidden-position budgets imply an allowed
palette bijection whenever every possible Hall rectangle exceeds the total. -/
theorem palette_equiv_of_budgets (R : A → B → Prop) (n r c t : ℕ)
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hrow : ∀ x, (Finset.univ.filter (R x)).card ≤ r)
    (hcol : ∀ y, (Finset.univ.filter (fun x => R x y)).card ≤ c)
    (htotal : (Finset.univ.filter (fun p : A × B => R p.1 p.2)).card ≤ t)
    (harith : ∀ s u : ℕ, 0 < s → 0 < u → s ≤ c → u ≤ r → n < s+u → t < s*u) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  apply palette_equiv_of_no_rectangle R (hA.trans hB.symm)
  intro S T hsum
  by_contra! hn
  have hSc : S.card ≤ n := (Finset.card_le_univ _).trans_eq hA
  have hTc : T.card ≤ n := (Finset.card_le_univ _).trans_eq hB
  have hSp : 0 < S.card := by rw [hB] at hsum; omega
  have hTp : 0 < T.card := by rw [hB] at hsum; omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hSp
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hTp
  have hr : T.card ≤ r := (Finset.card_le_card (show T ⊆ Finset.univ.filter (R x) from
    fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn x hx z hz⟩)).trans (hrow x)
  have hc : S.card ≤ c := (Finset.card_le_card (show S ⊆ Finset.univ.filter (fun x => R x y) from
    fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn z hz y hy⟩)).trans (hcol y)
  have hp : S.card * T.card ≤ t := by
    have hh := Finset.card_le_card (show S ×ˢ T ⊆ Finset.univ.filter (fun p : A × B => R p.1 p.2) from by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn p.1 (Finset.mem_product.mp hp).1
        p.2 (Finset.mem_product.mp hp).2⟩)
    rw [Finset.card_product] at hh
    exact hh.trans htotal
  exact Nat.not_lt_of_ge hp (harith S.card T.card hSp hTp hc hr (by simpa only [hB] using hsum))

/-- G12's residual Hall step after three prescribed pairs. This is a proof
for every 17×17 matrix with these budgets, not enumeration of matrices. -/
theorem palette_cut_three (R : A → B → Prop)
    (hA : Fintype.card A = 17) (hB : Fintype.card B = 17)
    (hr : ∀ x, (Finset.univ.filter (R x)).card ≤ 9)
    (hc : ∀ y, (Finset.univ.filter (fun x => R x y)).card ≤ 9)
    (ht : (Finset.univ.filter (fun p : A × B => R p.1 p.2)).card ≤ 27) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  apply palette_equiv_of_budgets R 17 9 9 27 hA hB hr hc ht
  intro s u hs hu hsc hur hsum
  have hse : s = 9 := by omega
  have hue : u = 9 := by omega
  subst s; subst u; norm_num

/-- G12's residual Hall step after four prescribed pairs. -/
theorem palette_cut_four (R : A → B → Prop)
    (hA : Fintype.card A = 16) (hB : Fintype.card B = 16)
    (hr : ∀ x, (Finset.univ.filter (R x)).card ≤ 12)
    (hc : ∀ y, (Finset.univ.filter (fun x => R x y)).card ≤ 12)
    (ht : (Finset.univ.filter (fun p : A × B => R p.1 p.2)).card ≤ 36) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  apply palette_equiv_of_budgets R 16 12 12 36 hA hB hr hc ht
  intro s u hs hu hsc hur hsum
  have hs5 : 5 ≤ s := by omega
  interval_cases s <;> nlinarith

/-- G12's five-matching-cut residual Hall step, once the exceptional row
or column has been handled by the prescribed pairs. -/
theorem palette_cut_five (R : A → B → Prop)
    (hA : Fintype.card A = 15) (hB : Fintype.card B = 15)
    (hr : ∀ x, (Finset.univ.filter (R x)).card ≤ 12)
    (hc : ∀ y, (Finset.univ.filter (fun x => R x y)).card ≤ 12)
    (ht : (Finset.univ.filter (fun p : A × B => R p.1 p.2)).card ≤ 45) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  apply palette_equiv_of_budgets R 15 12 12 45 hA hB hr hc ht
  intro s u hs hu hsc hur hsum
  have hs4 : 4 ≤ s := by omega
  interval_cases s <;> nlinarith

/-- G12's independent-separator palette lemma, with at most four special
rows and four special columns. -/
theorem palette_special_four (R : A → B → Prop)
    (hA : Fintype.card A = 20) (hB : Fintype.card B = 20)
    (P : Finset A) (Q : Finset B) (hP : P.card ≤ 4) (hQ : Q.card ≤ 4)
    (hoff : ∀ x, x ∉ P → ∀ y, y ∉ Q → ¬ R x y)
    (hr : ∀ x, (Finset.univ.filter (R x)).card ≤ 16)
    (hc : ∀ y, (Finset.univ.filter (fun x => R x y)).card ≤ 16) :
    ∃ f : A ≃ B, ∀ x, ¬ R x (f x) := by
  apply palette_equiv_of_no_rectangle R (hA.trans hB.symm)
  intro S T hsum
  by_contra! hn
  have hSc : S.card ≤ 20 := (Finset.card_le_univ _).trans_eq hA
  have hTc : T.card ≤ 20 := (Finset.card_le_univ _).trans_eq hB
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < S.card by rw [hB] at hsum; omega)
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < T.card by rw [hB] at hsum; omega)
  have hSr : S.card ≤ 16 := (Finset.card_le_card (show S ⊆ Finset.univ.filter (fun x => R x y) from
    fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn z hz y hy⟩)).trans (hc y)
  have hTr : T.card ≤ 16 := (Finset.card_le_card (show T ⊆ Finset.univ.filter (R x) from
    fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn x hx z hz⟩)).trans (hr x)
  have hSP : P.card < S.card := by rw [hB] at hsum; omega
  have hTQ : Q.card < T.card := by rw [hB] at hsum; omega
  obtain ⟨a,ha,hap⟩ := Finset.exists_mem_notMem_of_card_lt_card hSP
  obtain ⟨b,hb,hbq⟩ := Finset.exists_mem_notMem_of_card_lt_card hTQ
  exact hoff a hap b hbq (hn a ha b hb)

end Se20Part
