import Se20Part.FiveCutPalette

noncomputable section
open scoped Classical
namespace Se20Part

/-- Complete prescribed pairs for matching cuts of sizes zero through four. -/
theorem palette_complete_small {C : Type*} [Fintype C] (hC : Fintype.card C = 20)
    (n : ℕ) (hn : n ≤ 4) (R : C → C → Prop) (x y : Fin n → C)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i, ¬ R (x i) (y i))
    (hr : ∀ c, (Finset.univ.filter (R c)).card ≤ 3*n)
    (hc : ∀ d, (Finset.univ.filter (fun c => R c d)).card ≤ 3*n)
    (ht : (Finset.univ.filter (fun p : C × C => R p.1 p.2)).card ≤ 9*n) :
    ∃ p : C ≃ C, (∀ i, p (x i) = y i) ∧ ∀ c, ¬ R c (p c) := by
  apply palette_complete_prescribed R x y hx hy hxy
  apply palette_equiv_of_budgets (fun (c : {c // c ∉ Set.range x})
    (d : {c // c ∉ Set.range y}) => R c.val d.val) (20-n) (3*n) (3*n) (9*n)
  · rw [Fintype.card_subtype_compl,hC,← Fintype.card_congr (Equiv.ofInjective x hx)]
    simp only [Fintype.card_fin]
  · rw [Fintype.card_subtype_compl,hC,← Fintype.card_congr (Equiv.ofInjective y hy)]
    simp only [Fintype.card_fin]
  · intro c
    apply le_trans _ (hr c.val)
    apply Finset.card_le_card_of_injOn (fun (d : {d // d ∉ Set.range y}) => d.val)
    · intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hd).2⟩
    · intro d _ e _ he; exact Subtype.ext he
  · intro d
    apply le_trans _ (hc d.val)
    apply Finset.card_le_card_of_injOn (fun (c : {c // c ∉ Set.range x}) => c.val)
    · intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2⟩
    · intro c _ e _ he; exact Subtype.ext he
  · apply le_trans _ ht
    apply Finset.card_le_card_of_injOn (fun p => (p.1.val,p.2.val))
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
    · intro p _ q _ he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  · intro s u hs hu hsc hur hsum
    interval_cases n
    · omega
    · omega
    · omega
    · have hs9 : s = 9 := by omega
      have hu9 : u = 9 := by omega
      subst s; subst u; norm_num
    · have hs5 : 5 ≤ s := by omega
      have hs12 : s ≤ 12 := by omega
      interval_cases s <;> nlinarith

theorem matching_cut_small_palette {C : Type*} [Fintype C] [DecidableEq C]
    (hC : Fintype.card C = 20) (n : ℕ) (hn : n ≤ 4)
    (S T L K : Fin n → Finset C)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hK : ∀ i, 8 ≤ (K i).card)
    (hdis : ∀ i, Disjoint (L i) (S i)) :
    ∃ (p : C ≃ C) (x y : Fin n → C),
      Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ p (x i) = y i) ∧
      ∀ c, ¬ starForbidden S T c (p c) := by
  obtain ⟨x,y,hx,hy,hmem⟩ := matching_cut_four_prescribed S T L K
    (by simpa using hn) hS hT hL hK hdis
  have row : ∀ (S T : Fin n → Finset C), (∀ i, (T i).card ≤ 3) →
      ∀ c, (Finset.univ.filter (starForbidden S T c)).card ≤ 3*n := by
    intro S T hT c
    apply (starForbidden_row S T 3 hT c).trans
    calc
      _ ≤ Fintype.card (Fin n) * 3 := Nat.mul_le_mul_right 3 (Finset.card_le_univ _)
      _ = 3*n := by simp only [Fintype.card_fin,Nat.mul_comm]
  obtain ⟨p,hp,hgood⟩ := palette_complete_small hC n hn (starForbidden S T) x y hx hy
    (fun i => (hmem i).2.2) (row S T hT)
    (by
      intro d
      convert row T S hS d using 1
      congr 1
      ext c
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact starForbidden_symm S T c d)
    (by simpa [Nat.mul_comm] using starForbidden_total S T 3 3 hS hT)
  exact ⟨p,x,y,hx,hy,fun i => ⟨(hmem i).1,(hmem i).2.1,hp i⟩,hgood⟩

end Se20Part
