import Se20Part.ForcedFiveCut

noncomputable section
open scoped Classical
namespace Se20Part

theorem subtype_filter_card {C : Type*} [Fintype C] (P Q : C → Prop) :
    (Finset.univ.filter (fun c : {c // P c} => Q c.val)).card =
      (Finset.univ.filter (fun c => P c ∧ Q c)).card := by
  apply Finset.card_bij (fun c _ => c.val)
  · intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c.prop,(Finset.mem_filter.mp hc).2⟩
  · intro c _ d _ he; exact Subtype.ext he
  · intro c hc
    obtain ⟨_,hp,hq⟩ := Finset.mem_filter.mp hc
    exact ⟨⟨c,hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩,rfl⟩

/-- Combine the prescribed bijection on the source colours with a bijection
on the remaining colours, retaining every prescribed pair. -/
theorem palette_complete_prescribed {I C : Type*} [Fintype I] [Fintype C]
    (R : C → C → Prop) (x y : I → C)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i, ¬ R (x i) (y i))
    (hrest : ∃ q : {c // c ∉ Set.range x} ≃ {c // c ∉ Set.range y},
      ∀ c, ¬ R c.val (q c).val) :
    ∃ p : C ≃ C, (∀ i, p (x i) = y i) ∧ ∀ c, ¬ R c (p c) := by
  obtain ⟨q,hq⟩ := hrest
  let e := (Equiv.ofInjective x hx).symm.trans (Equiv.ofInjective y hy)
  let p := Equiv.subtypeCongr e q
  have hp : ∀ c (hc : c ∈ Set.range x), p c = (e ⟨c,hc⟩).val := by
    intro c hc
    simp [p,Equiv.subtypeCongr,Equiv.sumCompl_symm_apply_of_pos hc]
  have hn : ∀ c (hc : c ∉ Set.range x), p c = (q ⟨c,hc⟩).val := by
    intro c hc
    simp [p,Equiv.subtypeCongr,Equiv.sumCompl_symm_apply_of_neg hc]
  have hi : ∀ i, p (x i) = y i := by
    intro i
    rw [hp _ ⟨i,rfl⟩]
    simp [e]
  refine ⟨p,hi,?_⟩
  intro c
  by_cases hc : c ∈ Set.range x
  · obtain ⟨i,rfl⟩ := hc
    rw [hi]
    exact hxy i
  · rw [hn _ hc]
    exact hq ⟨c,hc⟩

/-- Residual forbidden-position budgets are sufficient for extending the
five prescribed pairs to an allowed permutation of all twenty colours. -/
theorem palette_complete_five {C : Type*} [Fintype C] (hC : Fintype.card C = 20)
    (R : C → C → Prop) (x y : Fin 5 → C)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i, ¬ R (x i) (y i))
    (hr : ∀ c, (Finset.univ.filter (fun d => d ∉ Set.range y ∧ R c d)).card ≤ 12)
    (hc : ∀ d, (Finset.univ.filter (fun c => c ∉ Set.range x ∧ R c d)).card ≤ 12)
    (ht : (Finset.univ.filter (fun p : C × C => R p.1 p.2)).card ≤ 45) :
    ∃ p : C ≃ C, (∀ i, p (x i) = y i) ∧ ∀ c, ¬ R c (p c) := by
  apply palette_complete_prescribed R x y hx hy hxy
  apply palette_cut_five (fun (c : {c // c ∉ Set.range x})
    (d : {c // c ∉ Set.range y}) => R c.val d.val)
  · rw [Fintype.card_subtype_compl, hC, ← Fintype.card_congr (Equiv.ofInjective x hx)]
    rfl
  · rw [Fintype.card_subtype_compl, hC, ← Fintype.card_congr (Equiv.ofInjective y hy)]
    rfl
  · intro c
    apply le_trans _ (hr c.val)
    apply Finset.card_le_card_of_injOn (fun (d : {d // d ∉ Set.range y}) => d.val)
    · intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,d.prop,(Finset.mem_filter.mp hd).2⟩
    · intro d _ e _ he; exact Subtype.ext he
  · intro d
    apply le_trans _ (hc d.val)
    apply Finset.card_le_card_of_injOn (fun (c : {c // c ∉ Set.range x}) => c.val)
    · intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c.prop,(Finset.mem_filter.mp hc).2⟩
    · intro c _ e _ he; exact Subtype.ext he
  · apply le_trans _ ht
    apply Finset.card_le_card_of_injOn (fun p => (p.1.val,p.2.val))
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
    · intro p _ q _ he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))

end Se20Part
