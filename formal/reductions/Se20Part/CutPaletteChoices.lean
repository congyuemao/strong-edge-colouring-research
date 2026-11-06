import Se20Part.PaletteExtension

noncomputable section
open scoped Classical
namespace Se20Part

/-- An SDR with an explicit finite domain. -/
theorem representatives_of_card {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (hL : ∀ i, Fintype.card I ≤ (L i).card) :
    ∃ f : I → C, Function.Injective f ∧ ∀ i, f i ∈ L i := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp
  intro S
  rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  · exact (Finset.card_le_univ S).trans ((hL i).trans (Finset.card_le_card
      (Finset.subset_biUnion_of_mem L hi)))

/-- Double counting star-colour incidences, also for a restricted colour set. -/
theorem star_incidence_count {I C : Type*} [Fintype I] [DecidableEq C]
    (S : I → Finset C) (M : Finset C) :
    ∑ c ∈ M, (Finset.univ.filter (fun i => c ∈ S i)).card =
      ∑ i : I, (M ∩ S i).card := by
  simp only [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A colour occurring in at least two stars consumes at least two incidences. -/
theorem repeated_colours_bound {I C : Type*} [Fintype I] [DecidableEq C]
    (S : I → Finset C) (M : Finset C) (b : ℕ)
    (hS : ∀ i, (S i).card ≤ b)
    (hM : ∀ c ∈ M, 2 ≤ (Finset.univ.filter (fun i => c ∈ S i)).card) :
    2 * M.card ≤ Fintype.card I * b := by
  calc
    2 * M.card = ∑ _c ∈ M, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ M, (Finset.univ.filter (fun i => c ∈ S i)).card :=
      Finset.sum_le_sum hM
    _ = ∑ i : I, (M ∩ S i).card := star_incidence_count S M
    _ ≤ ∑ _i : I, b := Finset.sum_le_sum (fun i _ =>
      (Finset.card_le_card Finset.inter_subset_right).trans (hS i))
    _ = _ := by simp

/-- Greedy distinct representatives can avoid a row-dependent forbidden set. -/
theorem allowed_targets_of_rows {I A B : Type*} [Fintype I] [Fintype B]
    [DecidableEq B] (R : A → B → Prop) (x : I → A) (L : I → Finset B)
    (r : ℕ) (hr : ∀ i, (Finset.univ.filter (R (x i))).card ≤ r)
    (hL : ∀ i, Fintype.card I + r ≤ (L i).card) :
    ∃ y : I → B, Function.Injective y ∧ ∀ i, y i ∈ L i ∧ ¬ R (x i) (y i) := by
  let T := fun i => L i \ Finset.univ.filter (R (x i))
  obtain ⟨y, hy, hmem⟩ := representatives_of_card T (by
    intro i
    have h := Finset.le_card_sdiff (Finset.univ.filter (R (x i))) (L i)
    have := hr i
    have := hL i
    dsimp [T]
    omega)
  refine ⟨y, hy, fun i => ?_⟩
  have h := Finset.mem_sdiff.mp (hmem i)
  exact ⟨h.1, fun hr => h.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)⟩

/-- The actual union of star rectangles, with source colours first. -/
def starForbidden {I A B : Type*} (S : I → Finset A) (T : I → Finset B)
    (x : A) (y : B) : Prop := ∃ i, x ∈ S i ∧ y ∈ T i

theorem starForbidden_row {I A B : Type*} [Fintype I] [Fintype B]
    [DecidableEq B] (S : I → Finset A) (T : I → Finset B) (b : ℕ)
    (hT : ∀ i, (T i).card ≤ b) (x : A) :
    (Finset.univ.filter (starForbidden S T x)).card ≤
      (Finset.univ.filter (fun i => x ∈ S i)).card * b := by
  have he : Finset.univ.filter (starForbidden S T x) =
      (Finset.univ.filter (fun i => x ∈ S i)).biUnion T := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, starForbidden,
      Finset.mem_biUnion]
  rw [he]
  exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum (fun i _ => hT i)).trans_eq
    (by simp))

theorem starForbidden_total {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (S : I → Finset A) (T : I → Finset B)
    (a b : ℕ) (hS : ∀ i, (S i).card ≤ a) (hT : ∀ i, (T i).card ≤ b) :
    (Finset.univ.filter (fun p : A × B => starForbidden S T p.1 p.2)).card ≤
      Fintype.card I * (a * b) := by
  have he : Finset.univ.filter (fun p : A × B => starForbidden S T p.1 p.2) =
      Finset.univ.biUnion (fun i => S i ×ˢ T i) := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨i,hi,hj⟩ := (Finset.mem_filter.mp hp).2
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_product.mpr ⟨hi,hj⟩⟩
    · intro hp
      obtain ⟨i,_,hij⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,
        (Finset.mem_product.mp hij).1,(Finset.mem_product.mp hij).2⟩
  rw [he]
  calc
    _ ≤ ∑ i : I, (S i ×ˢ T i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, a * b := Finset.sum_le_sum (fun i _ => by
      rw [Finset.card_product]; exact Nat.mul_le_mul (hS i) (hT i))
    _ = _ := by simp

/-- For up to four matching cut edges, each source can be chosen in its
eight-colour list and in at most one boundary star. This supplies the
prescribed pairs; the stars and lists are arbitrary, not sampled inputs. -/
theorem matching_cut_four_prescribed {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] (S T L K : I → Finset C)
    (hn : Fintype.card I ≤ 4)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hK : ∀ i, 8 ≤ (K i).card)
    (hdis : ∀ i, Disjoint (L i) (S i)) :
    ∃ x y : I → C, Function.Injective x ∧ Function.Injective y ∧
      ∀ i, x i ∈ L i ∧ y i ∈ K i ∧ ¬ starForbidden S T (x i) (y i) := by
  let X : I → Finset C := fun i => (L i).filter
    (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1)
  have hX : ∀ i, Fintype.card I ≤ (X i).card := by
    intro i
    let M := (L i).filter (fun c => 2 ≤ (Finset.univ.filter (fun j => c ∈ S j)).card)
    have hc : 2 * M.card ≤ (Fintype.card I - 1) * 3 := by
      let U : {j : I // j ≠ i} → Finset C := fun j => S j.val
      have hocc : ∀ c ∈ M, 2 ≤ (Finset.univ.filter (fun j => c ∈ U j)).card := by
        intro c hc
        have hci : c ∉ S i := fun h => Finset.disjoint_left.mp (hdis i)
          (Finset.mem_filter.mp hc).1 h
        have he : (Finset.univ.filter (fun j => c ∈ U j)).card =
            (Finset.univ.filter (fun j => c ∈ S j)).card := by
          apply Finset.card_bij (fun j _ => j.val)
          · intro j hj; simpa [U] using hj
          · intro j _ k _ he; exact Subtype.ext he
          · intro j hj
            have hjc : c ∈ S j := (Finset.mem_filter.mp hj).2
            exact ⟨⟨j, fun he => hci (he ▸ hjc)⟩, by simpa [U] using hjc, rfl⟩
        rw [he]
        exact (Finset.mem_filter.mp hc).2
      have hb := repeated_colours_bound U M 3 (fun j => hS j.val) hocc
      simpa only [Fintype.card_subtype_compl, Fintype.card_unique] using hb
    have hm : M.card ≤ 4 := by omega
    have hp : (X i).card + M.card = (L i).card := by
      have he : M = (L i).filter (fun c => ¬
          (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1) := by
        ext c
        simp only [M, Finset.mem_filter, Nat.not_le, Nat.add_one_le_iff]
      rw [he]
      exact Finset.card_filter_add_card_filter_not _
    have := hL i
    omega
  obtain ⟨x, hx, hxL⟩ := representatives_of_card X hX
  have hr : ∀ i, (Finset.univ.filter (starForbidden S T (x i))).card ≤ 3 := by
    intro i
    apply (starForbidden_row S T 3 hT (x i)).trans
    have hh := Nat.mul_le_mul_right 3 (Finset.mem_filter.mp (hxL i)).2
    rw [Nat.one_mul] at hh
    convert hh using 2 <;> congr 2
  obtain ⟨y, hy, hyK⟩ := allowed_targets_of_rows (starForbidden S T) x K 3 hr
    (fun i => by have := hK i; omega)
  exact ⟨x,y,hx,hy,fun i => ⟨(Finset.mem_filter.mp (hxL i)).1,(hyK i).1,(hyK i).2⟩⟩

/-- The four-list Hall bound in the ordinary five-cut construction. -/
theorem five_stars_single_hall {C : Type*} [Fintype C] [DecidableEq C]
    (S L : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hdis : ∀ i, Disjoint (L i) (S i))
    (J : Finset (Fin 5)) (hJ : J.card ≤ 4) :
    J.card ≤ (J.biUnion (fun i => (L i).filter
      (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1))).card := by
  let M : Finset C := Finset.univ.filter
    (fun c => 2 ≤ (Finset.univ.filter (fun j => c ∈ S j)).card)
  let X := fun i => (L i).filter
    (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1)
  let U := J.biUnion X
  change J.card ≤ U.card
  by_contra hn
  have hJp : 0 < J.card := by omega
  have hM : M.card ≤ 7 := by
    have hh := repeated_colours_bound S M 3 hS
      (fun c hc => (Finset.mem_filter.mp hc).2)
    norm_num at hh
    omega
  have hb : ∀ i ∈ J, 8 + (M ∩ S i).card ≤ U.card + M.card := by
    intro i hi
    have hcover : L i ⊆ U ∪ (M \ S i) := by
      intro c hc
      by_cases hcm : c ∈ M
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hcm,fun hs => Finset.disjoint_left.mp (hdis i) hc hs⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i,hi,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
        have hnot : ¬ 2 ≤ (Finset.univ.filter (fun j => c ∈ S j)).card := by
          simpa only [M,Finset.mem_filter,Finset.mem_univ,true_and] using hcm
        omega
    have hle := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have he := Finset.card_sdiff_add_card_inter M (S i)
    have := hL i
    omega
  have hinc : 2 * M.card ≤ J.card * (U.card + M.card - 8) +
      (5 - J.card) * 3 := by
    calc
      2 * M.card = ∑ _c ∈ M, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ M, (Finset.univ.filter (fun i => c ∈ S i)).card :=
        Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
      _ = ∑ i : Fin 5, (M ∩ S i).card := star_incidence_count S M
      _ = (∑ i ∈ J, (M ∩ S i).card) +
          ∑ i ∈ Finset.univ \ J, (M ∩ S i).card := by
        exact (Finset.sum_add_sum_compl J _).symm
      _ ≤ (∑ _i ∈ J, (U.card + M.card - 8)) + ∑ _i ∈ Finset.univ \ J, 3 := by
        apply Nat.add_le_add
        · exact Finset.sum_le_sum (fun i hi => by have := hb i hi; omega)
        · exact Finset.sum_le_sum (fun i _ =>
            (Finset.card_le_card Finset.inter_subset_right).trans (hS i))
      _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ J)]
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hJp
  have hbase : 8 ≤ U.card + M.card := le_trans (Nat.le_add_right _ _) (hb i hi)
  have harith : ∀ k h u : ℕ, 1 ≤ k → k ≤ 4 → h ≤ 7 → u < k →
      8 ≤ u+h → 2*h ≤ k*(u+h-8)+(5-k)*3 → False := by
    intro k h u hk hk4 hh hu h8 hcount
    interval_cases k <;> omega
  exact harith J.card M.card U.card hJp hJ hM (by omega) hbase hinc

/-- Extend already assigned distinct representatives by Hall on the remaining
lists after deleting the assigned colours. -/
theorem representatives_extend {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (D : Finset I) (f : I → C)
    (hf : Set.InjOn f D) (hfL : ∀ i ∈ D, f i ∈ L i)
    (hh : ∀ J : Finset {i : I // i ∉ D},
      J.card ≤ (J.biUnion (fun i => L i.val \ D.image f)).card) :
    ∃ g : I → C, Function.Injective g ∧ (∀ i, g i ∈ L i) ∧ ∀ i ∈ D, g i = f i := by
  obtain ⟨g,hg,hgL⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun i : {i : I // i ∉ D} => L i.val \ D.image f)).mp hh
  let k : I → C := fun i => if hi : i ∈ D then f i else g ⟨i,hi⟩
  have hnew : ∀ i (hi : i ∉ D), g ⟨i,hi⟩ ∉ D.image f :=
    fun i hi => (Finset.mem_sdiff.mp (hgL ⟨i,hi⟩)).2
  refine ⟨k,?_,?_,?_⟩
  · intro i j he
    by_cases hi : i ∈ D <;> by_cases hj : j ∈ D
    · exact hf hi hj (by simpa only [k,dif_pos hi,dif_pos hj] using he)
    · exact False.elim (hnew j hj (Finset.mem_image.mpr
        ⟨i,hi,by simpa only [k,dif_pos hi,dif_neg hj] using he⟩))
    · exact False.elim (hnew i hi (Finset.mem_image.mpr
        ⟨j,hj,by simpa only [k,dif_neg hi,dif_pos hj] using he.symm⟩))
    · exact congrArg Subtype.val (hg (by simpa only [k,dif_neg hi,dif_neg hj] using he))
  · intro i
    by_cases hi : i ∈ D
    · simpa only [k,dif_pos hi] using hfL i hi
    · simpa only [k,dif_neg hi] using (Finset.mem_sdiff.mp (hgL ⟨i,hi⟩)).1
  · intro i hi; exact dif_pos hi

/-- Uniform bounds suffice to complete a partial SDR. -/
theorem representatives_extend_of_card {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I → Finset C) (D : Finset I) (f : I → C)
    (hf : Set.InjOn f D) (hfL : ∀ i ∈ D, f i ∈ L i)
    (hL : ∀ i, i ∉ D → Fintype.card I ≤ (L i).card) :
    ∃ g : I → C, Function.Injective g ∧ (∀ i, g i ∈ L i) ∧ ∀ i ∈ D, g i = f i := by
  apply representatives_extend L D f hf hfL
  intro J
  rcases J.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · simp
  · have hiL := hL i.val i.prop
    have hsub := Finset.subset_biUnion_of_mem
      (fun j : {j : I // j ∉ D} => L j.val \ D.image f) hi
    have hcard := Finset.card_le_card hsub
    have himage := Finset.card_image_le (s := D) (f := f)
    have hdiff := Finset.le_card_sdiff (D.image f) (L i.val)
    have hJ := Finset.card_le_univ J
    have hD := Finset.card_le_univ D
    rw [Fintype.card_subtype_compl, Fintype.card_coe] at hJ
    omega

end Se20Part
