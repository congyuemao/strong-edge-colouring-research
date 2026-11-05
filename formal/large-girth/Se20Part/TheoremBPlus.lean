import Se20Part.BadFamilies
import Se20Part.LocalLemma

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 1000000

theorem selected_part_injective {V I : Type} {G : SimpleGraph V} {E : Set G.edgeSet}
    (part : E → I) (f : I → E) (hf : ∀ i, part (f i) = i)
    {e e' : E} (he : e.val ∈ Set.range (fun i => (f i).val))
    (he' : e'.val ∈ Set.range (fun i => (f i).val)) (hh : part e = part e') : e = e' := by
  obtain ⟨i,hi⟩ := he
  obtain ⟨j,hj⟩ := he'
  have hi' : f i = e := Subtype.ext hi
  have hj' : f j = e' := Subtype.ext hj
  have hij : i = j := (hf i).symm.trans ((congrArg part hi').trans
    (hh.trans ((congrArg part hj').symm.trans (hf j))))
  exact hi'.symm.trans (hij ▸ hj')

theorem no_pairs_separated {V I : Type} {G : SimpleGraph V} {E : Set G.edgeSet}
    (part : E → I) (f : I → E) (hf : ∀ i, part (f i) = i)
    (hbad : ∀ b : PairBad G E part, ¬ ∀ e ∈ b.val, e ∈ Set.range f) :
    Separated G 5 (Set.range (fun i => (f i).val)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hne hclose
  have hij : i ≠ j := fun h => hne (congrArg (fun i => (f i).val) h)
  let b : PairBad G E part := ⟨{f i,f j},f i,f j,by simpa [hf] using hij,rfl,hclose⟩
  apply hbad b
  intro e he
  simp only [b,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨i,rfl⟩
  · exact ⟨j,rfl⟩

theorem no_chains_option_forest {V I : Type} [Fintype V] {G : SimpleGraph V}
    (hg : GirthAtLeast G 5710) {E : Set G.edgeSet} (part : E → I)
    (f : I → E) (hf : ∀ i, part (f i) = i)
    (hs : Separated G 5 (Set.range (fun i => (f i).val)))
    (hbad : ∀ b : ChainBad G E part, ¬ ∀ e ∈ b.val, e ∈ Set.range f)
    (M : Set G.edgeSet) : (optionGraph G (Set.range (fun i => (f i).val)) M).IsAcyclic := by
  let D : Set G.edgeSet := Set.range (fun i => (f i).val)
  intro v Z hz
  have hZ : 5710 ≤ Z.length := by
    simpa using hg v (Z.mapLe (optionGraph_le G D M)) (hz.mapLe _)
  let Y := (Z.take 2854).mapLe (optionGraph_le G D M)
  have hY : Y.IsPath := (hz.isPath_take (by omega)).mapLe _
  have hlen : Y.length = 2854 := by simp [Y,Walk.take_length,Nat.min_eq_left (by omega : 2854 ≤ Z.length)]
  obtain ⟨_,⟨F⟩⟩ := lemma_3_15 hg (by norm_num) hs Z hz Y hY (by rw [hlen]; norm_num)
    (by simpa [Y,Walk.support_mapLe_eq_support,Walk.support_take] using List.take_subset (2854+1) Z.support)
    (by simpa [Y,Walk.edges_mapLe_eq_edges,Walk.edges_take] using List.take_subset 2854 Z.edges)
  obtain ⟨F',hsub,hpos⟩ := F.distinct_positions
  have hsubD : F'.edges ⊆ D := F'.subset
  let S : Finset E := (Subtype.val ⁻¹' F'.edges).toFinset
  have hS (e : E) : e ∈ S ↔ e.val ∈ F'.edges := by simp [S]
  have hreal : realFamily S = F'.edges := by
    ext e
    constructor
    · rintro ⟨e',he',rfl⟩
      exact (hS e').mp he'
    · intro he
      obtain ⟨i,hi⟩ := hsubD he
      exact ⟨f i,(hS (f i)).mpr (by simpa [hi] using he),hi⟩
  have hSn : S.Nonempty := by
    obtain ⟨r,_,_,_,_⟩ := F'.spans 0 (by omega)
    have hr : r.val ∈ realFamily S := by rw [hreal]; exact r.property
    obtain ⟨e,he,_⟩ := hr
    exact ⟨e,he⟩
  have hinj : Set.InjOn part (S : Set E) := by
    intro e he e' he' h
    exact selected_part_injective part f hf
      (hsubD ((hS e).mp he)) (hsubD ((hS e').mp he')) h
  have hlong : LongSpanning G (realFamily S) := by
    rw [hreal]
    let F₀ : SpanningFamily F'.edges Y := { F' with subset := fun _ he => he }
    exact ⟨fun e he e' he' h => hs e (hsubD he) e' (hsubD he') h,_,_,Y,hY,hlen,F₀,rfl,hpos⟩
  let b : ChainBad G E part := ⟨S,hSn,hinj,hlong⟩
  apply hbad b
  intro e he
  obtain ⟨i,hi⟩ := hsubD ((hS e).mp he)
  exact ⟨i,Subtype.ext hi⟩

/-- Both kinds of bad events are finite, and zero-probability selections from
one part twice are absent by construction. -/
theorem random_sparse_forest_transversal {V I : Type} [Fintype V] [Fintype I]
    (lll : LovaszLocalLemma) (hcount : TransferMatrixSpanningFamilyBound)
    (hnum : TransferMatrix5710Bound exp31Matrix5710) {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5710)
    (E : Set G.edgeSet) (part : E → I) (hsurj : Function.Surjective part)
    (hsize : ∀ i, 5710 ≤ partSize part i) :
    ∃ f : I → E, (∀ i, part (f i) = i) ∧
      Separated G 5 (Set.range (fun i => (f i).val)) ∧
      ∀ M, (optionGraph G (Set.range (fun i => (f i).val)) M).IsAcyclic := by
  let B := Sum (PairBad G E part) (ChainBad G E part)
  let family : B → Finset E := Sum.elim Subtype.val Subtype.val
  let C : ℝ := 726*(1203/1000)*(t5710 : ℝ) + (transferContribution5710 exp31Matrix5710 : ℝ)
  have hC (i : I) : ∑ b ∈ Finset.univ.filter (fun b => i ∈ (family b).image part),
      familyWeight part (1203/1000) (family b) ≤ C := by
    have hp := closePair_weight_bound hd E part hsize i
    have hq := hcount V I G hd hg E part hsurj hsize i
    dsimp only [B,family]
    rw [Finset.sum_filter,Fintype.sum_sum_type]
    simpa only [C,Finset.sum_filter,Sum.elim_inl,Sum.elim_inr,familyWeight,partSize,
      ← Nat.card_eq_fintype_card] using add_le_add hp hq
  have hlog : C / (1-(t5710 : ℝ)) ≤ Real.log (1203/1000) := by
    have hn := (exp31_numerical_suffices hnum).le
    convert hn using 1
    simp only [C,lllRhs5710,Rat.cast_mul,Rat.cast_inv,Rat.cast_sub,Rat.cast_one,Rat.cast_add]
    norm_num [beta5710]
    ring
  obtain ⟨f,hf,hbad⟩ := random_transversal_of_weight_bound lll part hsurj hsize family
    (by rintro (b|b); exact b.property.nonempty; exact b.property.1)
    (by rintro (b|b); exact b.property.injOn; exact b.property.2.1) C hC hlog
  have hp : ∀ b : PairBad G E part, ¬ ∀ e ∈ b.val, e ∈ Set.range f := fun b => hbad (.inl b)
  have hq : ∀ b : ChainBad G E part, ¬ ∀ e ∈ b.val, e ∈ Set.range f := fun b => hbad (.inr b)
  have hs := no_pairs_separated part f hf hp
  exact ⟨f,hf,hs,no_chains_option_forest hg part f hf hs hq⟩

theorem acyclic_isPseudoforest {V : Type*} {G : SimpleGraph V} (h : G.IsAcyclic) :
    IsPseudoforest G := by
  intro C u v p q hp hq
  exact (h (p.map C.toSimpleGraph_hom) (hp.map (fun x y hxy => Subtype.ext hxy))).elim

/-- Theorem 3.14 with the two explicitly retained transfer-matrix hypotheses:
the concrete rational bound and the weighted spanning-family counting bound.
The graph decomposition, geometry, event independence, LLL application, and
twenty-colour assembly are proved here. Haxell is not an assumption. -/
theorem theorem_B_plus {V : Type} [Fintype V] (kost : Kostochka) (lll : LovaszLocalLemma)
    (hcount : TransferMatrixSpanningFamilyBound)
    (hnum : TransferMatrix5710Bound exp31Matrix5710)
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5710) :
    StrongColourable G 20 := by
  obtain ⟨c,a,b,he,ha,hb⟩ := directed_two_degree_decomposition G hd
  let H := factorLine G c
  have hdeg : DegreeLE H 2 := factorLine_degree c a b he ha hb
  have hHg : GirthAtLeast H 5710 := factorLine_girth c a b he ha hb hg
  let I := CyclicComponent H
  letI : Finite I := by unfold I CyclicComponent; infer_instance
  letI : Fintype I := Fintype.ofFinite I
  let E : Set G.edgeSet := {e | ∃ C : I, e ∈ C.val.supp}
  let part : E → I := fun e => e.property.choose
  have mempart (e : E) : e.val ∈ (part e).val.supp := e.property.choose_spec
  have parteq (e : E) (C : I) (h : e.val ∈ C.val.supp) : part e = C :=
    Subtype.ext (ConnectedComponent.eq_of_common_vertex (mempart e) h)
  have surj : Function.Surjective part := by
    intro C
    obtain ⟨e,he⟩ := C.val.nonempty_supp
    exact ⟨⟨e,C,he⟩,parteq _ C he⟩
  have hsize (C : I) : 5710 ≤ partSize part C := by
    let eqv : {e // part e = C} ≃ C.val.supp :=
      { toFun := fun e => ⟨e.val.val,by have hh := mempart e.val; rwa [e.property] at hh⟩
        invFun := fun e => ⟨⟨e.val,C,e.property⟩,parteq _ C e.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change 5710 ≤ Fintype.card {e // part e = C}
    rw [← Nat.card_eq_fintype_card,Nat.card_congr eqv]
    exact cyclicComponent_size hHg C
  obtain ⟨f,hf,hs,hU⟩ := random_sparse_forest_transversal lll hcount hnum hd hg E part surj
    (fun C => by
      have hh := hsize C
      simpa only [partSize,← Nat.card_eq_fintype_card] using hh)
  let d : I → G.edgeSet := fun C => (f C).val
  have hmem (C : I) : d C ∈ C.val.supp := by
    have hh := mempart (f C)
    rwa [hf C] at hh
  have hforest := cycle_cut_forest hdeg d hmem
  obtain ⟨M,hm,hcover,hdisj⟩ := four_matchings_of_factor_forest c (Set.range d) hforest
  exact proposition_3_13 kost G hd (hg.mono (by decide)) (Set.range d) M hs hm hcover (hdisj 3)
    (acyclic_isPseudoforest (hU (M 3)))

/-- Since the local lemma is now proved, only Kostochka and the two explicit
transfer-matrix bounds remain in this strengthened corollary. -/
theorem theorem_B_plus_of_transfer_bounds {V : Type} [Fintype V] (kost : Kostochka)
    (hcount : TransferMatrixSpanningFamilyBound)
    (hnum : TransferMatrix5710Bound exp31Matrix5710)
    (G : SimpleGraph V) (hd : MaxDegreeFour G) (hg : GirthAtLeast G 5710) :
    StrongColourable G 20 := theorem_B_plus kost lovasz_local_lemma hcount hnum G hd hg

end Se20Part
