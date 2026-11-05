import Se20Part.RandomTransversal

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 2000000

theorem sum_filter_subtype {X : Type} [Fintype X] (p : X → Prop) [DecidablePred p] (f : X → ℝ) :
    (∑ x ∈ Finset.univ.filter p, f x) = ∑ x : {x // p x}, f x.val := by
  exact Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) f

def realFamily {V : Type} {G : SimpleGraph V} {E : Set G.edgeSet} (S : Finset E) : Set G.edgeSet :=
  Subtype.val '' (S : Set E)

def ClosePair {V I : Type} (G : SimpleGraph V) (E : Set G.edgeSet) (part : E → I)
    (S : Finset E) : Prop :=
  ∃ e f : E, part e ≠ part f ∧ S = {e,f} ∧ EdgeWithin G 4 e.val f.val

def LongSpanning {V : Type} (G : SimpleGraph V) (D : Set G.edgeSet) : Prop :=
  Separated G 5 D ∧ ∃ u v, ∃ Y : G.Walk u v, Y.IsPath ∧ Y.length = 2854 ∧
    ∃ F : SpanningFamily D Y, F.edges = D ∧ Function.Injective (fun r => (F.projection r).pos)

abbrev PairBad {V I : Type} (G : SimpleGraph V) (E : Set G.edgeSet) (part : E → I) :=
  {S : Finset E // ClosePair G E part S}

abbrev ChainBad {V I : Type} (G : SimpleGraph V) (E : Set G.edgeSet) (part : E → I) :=
  {S : Finset E // S.Nonempty ∧ Set.InjOn part (S : Set E) ∧ LongSpanning G (realFamily S)}

theorem ClosePair.nonempty {V I : Type} {G : SimpleGraph V} {E : Set G.edgeSet} {part : E → I}
    {S : Finset E} (h : ClosePair G E part S) : S.Nonempty := by
  obtain ⟨e,f,_,rfl,_⟩ := h
  exact ⟨e,by simp⟩

theorem ClosePair.injOn {V I : Type} {G : SimpleGraph V} {E : Set G.edgeSet} {part : E → I}
    {S : Finset E} (h : ClosePair G E part S) : Set.InjOn part (S : Set E) := by
  obtain ⟨e,f,hne,rfl,_⟩ := h
  intro a ha b hb heq
  simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | exact (hne heq).elim | exact (hne heq.symm).elim

theorem closePair_orient {V I : Type} {G : SimpleGraph V} {E : Set G.edgeSet} {part : E → I}
    {S : Finset E} (h : ClosePair G E part S) {i : I} (hi : i ∈ S.image part) :
    ∃ e : {e // part e = i}, ∃ f : (separationGraph G E part 4).neighborSet e.val,
      S = {e.val,f.val} := by
  obtain ⟨e,f,hne,rfl,hclose⟩ := h
  simp only [Finset.image_insert,Finset.image_singleton,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨⟨e,rfl⟩,⟨f,hne,hclose⟩,rfl⟩
  · exact ⟨⟨f,rfl⟩,⟨e,Ne.symm hne,hclose.symm⟩,by ext; simp [or_comm]⟩

/-- The first class of bad events has total weight at most 726 β t at every
variable. Pairs from the same part are excluded in `ClosePair`. -/
theorem closePair_weight_bound {V I : Type} [Fintype V] [Fintype I] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (E : Set G.edgeSet) (part : E → I)
    (hsize : ∀ i, 5710 ≤ partSize part i) (i : I) :
    ∑ b ∈ Finset.univ.filter (fun b : PairBad G E part => i ∈ b.val.image part),
      familyWeight part (1203/1000) b.val ≤ 726*(1203/1000)*(t5710 : ℝ) := by
  rw [sum_filter_subtype (fun b : PairBad G E part => i ∈ b.val.image part)
    (fun b => familyWeight part (1203/1000) b.val)]
  let B := {b : PairBad G E part // i ∈ b.val.image part}
  choose e f he using fun b : B => closePair_orient b.val.property b.property
  let φ : B → Σ e : {e // part e = i}, (separationGraph G E part 4).neighborSet e.val :=
    fun b => ⟨e b,f b⟩
  have hφ : Function.Injective φ := by
    intro b c h
    have hh := congrArg (fun x : Σ e : {e // part e = i}, (separationGraph G E part 4).neighborSet e.val =>
      ({x.1.val,x.2.val} : Finset E)) h
    apply Subtype.ext
    apply Subtype.ext
    exact (he b).trans (hh.trans (he c).symm)
  have hcard : Fintype.card B ≤ partSize part i * 726 := by
    calc
      Fintype.card B ≤ Fintype.card (Σ e : {e // part e = i}, (separationGraph G E part 4).neighborSet e.val) :=
        Fintype.card_le_of_injective φ hφ
      _ = ∑ e : {e // part e = i}, Fintype.card ((separationGraph G E part 4).neighborSet e.val) := Fintype.card_sigma
      _ ≤ ∑ _e : {e // part e = i}, 726 := by
        apply Finset.sum_le_sum
        intro e he
        simpa only [Nat.card_eq_fintype_card,show 3^(4+2)-3 = 726 by norm_num] using separationGraph_degree hd E part 4 e.val
      _ = partSize part i * 726 := by simp [partSize]
  have hsizepos : (0 : ℝ) < partSize part i := by exact_mod_cast (show 0 < partSize part i by have := hsize i; omega)
  have hbound (b : B) : familyWeight part (1203/1000) b.val.val ≤
      ((1203/1000 : ℝ) / partSize part i) * (t5710 : ℝ) := by
    have hf := (f b).property
    change part (e b).val ≠ part (f b).val ∧ _ at hf
    have hsingle := (familyWeight_bounds part hsize {(f b).val} (by simp)).2
    have hsingle' : (1203/1000 : ℝ) / partSize part (part (f b).val) ≤ (t5710 : ℝ) := by
      simpa [familyWeight] using hsingle
    rw [familyWeight,he b,Finset.image_insert,Finset.image_singleton,
      Finset.prod_insert (by simpa using hf.1),Finset.prod_singleton,(e b).property]
    exact mul_le_mul_of_nonneg_left hsingle' (by positivity)
  have hsum : ∑ b : B, familyWeight part (1203/1000) b.val.val ≤
      (Fintype.card B : ℝ) * (((1203/1000 : ℝ) / partSize part i) * (t5710 : ℝ)) := by
    have hh : (∑ b : B, familyWeight part (1203/1000) b.val.val) ≤
        ∑ _b : B, (((1203/1000 : ℝ) / partSize part i) * (t5710 : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hbound b)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have hcount : (Fintype.card B : ℝ) ≤ (partSize part i : ℝ) * 726 := by exact_mod_cast hcard
  have ht : (0 : ℝ) ≤ t5710 := by norm_num [t5710,beta5710]
  have hh := hsum.trans (mul_le_mul_of_nonneg_right hcount (by positivity))
  have heq : ((partSize part i : ℝ)*726) * (((1203/1000 : ℝ)/partSize part i)*(t5710 : ℝ)) =
      726*(1203/1000)*(t5710 : ℝ) := by field_simp
  rw [heq] at hh
  exact hh

/-- Explicit remaining counting correspondence: the weighted count of distinct,
part-injective spanning families is bounded by the supplied transfer-matrix
convolution. This includes their embeddings in the degree-four graph, not only
the scalar depth-pattern identity. It is a named hypothesis, not an axiom. -/
def TransferMatrixSpanningFamilyBound : Prop :=
  ∀ (V I : Type) [Fintype V] [Fintype I] (G : SimpleGraph V), MaxDegreeFour G → GirthAtLeast G 5710 →
    ∀ (E : Set G.edgeSet) (part : E → I), Function.Surjective part →
      (∀ i, 5710 ≤ partSize part i) → ∀ i,
        (∑ b ∈ Finset.univ.filter (fun b : ChainBad G E part => i ∈ b.val.image part),
          familyWeight part (1203/1000) b.val) ≤ (transferContribution5710 exp31Matrix5710 : ℝ)

end Se20Part
