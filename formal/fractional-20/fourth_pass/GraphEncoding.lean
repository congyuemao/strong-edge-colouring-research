import fourth_pass.SelectedTriangle
import fourth_pass.PackedSoundness
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Se20Fractional.FourthPass.Encoding
open Finset Packed
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_internal_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (e : Sym2 V) :
    e ∈ internalEdges G R ↔ e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ R := by
  simp [internalEdges]

noncomputable def graphBits {n : Nat} (G : SimpleGraph (Fin n)) : Finset Nat :=
  ((univ ×ˢ univ).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image
    (fun p => n*p.1.val+p.2.val)
noncomputable def encodeGraph {n : Nat} (G : SimpleGraph (Fin n)) : Nat :=
  Finset.equivBitIndices.symm (graphBits G)

theorem testBit_encode {n : Nat} (G : SimpleGraph (Fin n)) (i : Nat) :
    (encodeGraph G).testBit i = true ↔ i ∈ graphBits G := by
  have he := Finset.equivBitIndices.apply_symm_apply (graphBits G)
  change (encodeGraph G).bitIndices.toFinset = graphBits G at he
  rw [← he]
  simp

theorem encoded_adj_iff {n : Nat} (G : SimpleGraph (Fin n)) (a b : Nat) :
    adjacent n (encodeGraph G) a b = true ↔
      ∃ u v : Fin n, u.val = a ∧ v.val = b ∧ G.Adj u v := by
  rw [adjacent_iff,testBit_encode]
  constructor
  · rintro ⟨hi,hb⟩
    obtain ⟨⟨u,v⟩,huv,heq⟩ := mem_image.mp hi
    have huv' : G.Adj u v := (mem_filter.mp huv).2
    obtain ⟨hua,hvb⟩ := (pair_index_inj v.isLt hb).mp heq
    exact ⟨u,v,hua,hvb,huv'⟩
  · rintro ⟨u,v,rfl,rfl,huv⟩
    exact ⟨mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨by simp,huv⟩,rfl⟩,v.isLt⟩

theorem encoded_adj {n : Nat} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    adjacent n (encodeGraph G) a.val b.val = true ↔ G.Adj a b := by
  rw [encoded_adj_iff]
  constructor
  · rintro ⟨u,v,hu,hv,huv⟩
    have hua : u = a := Fin.ext hu
    have hvb : v = b := Fin.ext hv
    simpa [hua,hvb] using huv
  · intro hab
    exact ⟨a,b,rfl,rfl,hab⟩

theorem encoded_symm {n : Nat} (G : SimpleGraph (Fin n)) (a b : Nat) :
    adjacent n (encodeGraph G) a b = adjacent n (encodeGraph G) b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [encoded_adj_iff]
  constructor <;> rintro ⟨u,v,hu,hv,huv⟩
  · exact ⟨v,u,hv,hu,huv.symm⟩
  · exact ⟨v,u,hv,hu,huv.symm⟩

theorem encoded_irrefl {n : Nat} (G : SimpleGraph (Fin n)) (a : Nat) :
    adjacent n (encodeGraph G) a a = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  obtain ⟨u,v,hu,hv,huv⟩ := (encoded_adj_iff G a a).mp ha
  have he : u = v := Fin.ext (hu.trans hv.symm)
  exact huv.ne he

theorem bits_card_le {n : Nat} {x : Nat} (S : Finset (Fin n))
    (hx : ∀ i, x.testBit i = true → ∃ v ∈ S, v.val = i) :
    pop n x ≤ S.card := by
  have hs : x.bitIndices.toFinset ⊆ S.image Fin.val := by
    intro i hi
    have hi' : x.testBit i = true := by simpa using hi
    obtain ⟨v,hv,hvi⟩ := hx i hi'
    exact mem_image.mpr ⟨v,hv,hvi⟩
  have hc := (card_le_card hs).trans (card_image_le : (S.image Fin.val).card ≤ S.card)
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup] at hc
  rw [pop_eq_min]
  omega

theorem encoded_degree_le {n : Nat} (G : SimpleGraph (Fin n)) (a : Fin n) :
    pop n (row n (encodeGraph G) a.val) ≤ G.degree a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply bits_card_le
  intro i hi
  have hadj : adjacent n (encodeGraph G) a.val i = true := by
    simpa only [adjacent,bne_iff_ne,band_bit_nonzero] using hi
  obtain ⟨u,v,hu,hv,huv⟩ := (encoded_adj_iff G a.val i).mp hadj
  have hua : u = a := Fin.ext hu
  subst u
  exact ⟨v,by simpa using huv,hv⟩

theorem encoded_common_le {n : Nat} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    pop n (row n (encodeGraph G) a.val &&& row n (encodeGraph G) b.val) ≤
      commonCount G a b := by
  apply bits_card_le
  intro i hi
  simp only [Nat.testBit_and,Bool.and_eq_true] at hi
  have ha : adjacent n (encodeGraph G) a.val i = true := by
    simpa only [adjacent,bne_iff_ne,band_bit_nonzero] using hi.1
  have hb : adjacent n (encodeGraph G) b.val i = true := by
    simpa only [adjacent,bne_iff_ne,band_bit_nonzero] using hi.2
  obtain ⟨u,v,hu,hv,huv⟩ := (encoded_adj_iff G a.val i).mp ha
  have hua : u = a := Fin.ext hu
  subst u
  have hb' : G.Adj b v := (encoded_adj G b v).mp (hv.symm ▸ hb)
  exact ⟨v,by simp [huv,hb'],hv⟩

noncomputable def lowerNeighbours {n : Nat} (G : SimpleGraph (Fin n))
    (R : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  R.filter (fun b => a ∈ R ∧ G.Adj a b ∧ b < a)

theorem sum_lowerNeighbours {n : Nat} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) :
    (∑ a : Fin n, (lowerNeighbours G R a).card) = (internalEdges G R).card := by
  rw [← card_sigma]
  apply card_bij (fun (p : (a : Fin n) × Fin n) _ => s(p.1,p.2))
  · intro p hp
    obtain ⟨_,hp⟩ := mem_sigma.mp hp
    obtain ⟨hb,ha,hab,_⟩ := mem_filter.mp hp
    refine (mem_internal_iff G R _).mpr ⟨hab,?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  · intro p hp q hq heq
    have hp' := (mem_filter.mp (mem_sigma.mp hp).2).2.2.2
    have hq' := (mem_filter.mp (mem_sigma.mp hq).2).2.2.2
    rcases Sym2.eq_iff.mp heq with he | he
    · cases p; cases q; simp_all
    · have ha : p.1 = q.2 := he.1
      have hb : p.2 = q.1 := he.2
      rw [ha,hb] at hp'
      exact False.elim (lt_asymm hp' hq')
  · intro e he
    obtain ⟨heG,hR⟩ := (mem_internal_iff G R e).mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := heG
      have ha := hR a (by simp)
      have hb := hR b (by simp)
      rcases lt_or_gt_of_ne hab.ne with hlt | hgt
      · refine ⟨⟨b,a⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨ha,hb,hab.symm,hlt⟩⟩,?_⟩
        exact Sym2.eq_swap
      · exact ⟨⟨a,b⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨hb,ha,hab,hgt⟩⟩,rfl⟩

theorem internal_le_sum_lower {n : Nat} (G : SimpleGraph (Fin n)) (r : Nat)
    (R : Finset (Fin n))
    (hr : ∀ i, r.testBit i = true → ∃ v ∈ R, v.val = i) :
    internal n (encodeGraph G) r n ≤ ∑ a : Fin n, (lowerNeighbours G R a).card := by
  have hbound (a : Fin n) :
      (if (r &&& bit a.val) == 0 then 0 else
        pop n (row n (encodeGraph G) a.val &&& r &&& mask a.val)) ≤
        (lowerNeighbours G R a).card := by
    split_ifs with hzero
    · omega
    · have haBit : r.testBit a.val = true :=
        (band_bit_nonzero r a.val).mp (by simpa only [beq_iff_eq] using hzero)
      obtain ⟨v,hv,hva⟩ := hr a.val haBit
      have hva' : v = a := Fin.ext hva
      subst v
      apply bits_card_le
      intro i hi
      simp only [Nat.testBit_and,Bool.and_eq_true,mask,bit_eq_pow,
        Nat.testBit_two_pow_sub_one,decide_eq_true_eq] at hi
      obtain ⟨b,hb,hbi⟩ := hr i hi.1.2
      have hab : G.Adj a b := by
        apply (encoded_adj G a b).mp
        simp only [adjacent,bne_iff_ne,band_bit_nonzero]
        simpa [hbi] using hi.1.1
      exact ⟨b,mem_filter.mpr ⟨hb,hv,hab,by change b.val < a.val; omega⟩,hbi⟩
  have heq : internal n (encodeGraph G) r n =
      ∑ a : Fin n, (if (r &&& bit a.val) == 0 then 0 else
        pop n (row n (encodeGraph G) a.val &&& r &&& mask a.val)) := by
    let f (a : Nat) := if (r &&& bit a) == 0 then 0 else
      pop n (row n (encodeGraph G) a &&& r &&& mask a)
    have hrange (k : Nat) : internal n (encodeGraph G) r k = ∑ a ∈ range k, f a := by
      induction k with
      | zero => simp [internal]
      | succ k ih => simp only [internal,sum_range_succ,ih,f]
    rw [hrange n]
    exact (Fin.sum_univ_eq_sum_range f n).symm
  rw [heq]
  exact sum_le_sum (fun a _ => hbound a)

theorem encoded_low {n : Nat} (G : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : G.Adj a b)
    (hl : 4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card ≤ 4) :
    low n (encodeGraph G) (a.val,b.val) = true := by
  let r := (row n (encodeGraph G) a.val ||| row n (encodeGraph G) b.val) &&&
    (mask n ^^^ bit a.val ^^^ bit b.val)
  have hne : a.val ≠ b.val := fun h => hab.ne (Fin.ext h)
  have hr : ∀ i, r.testBit i = true → ∃ v ∈ endpointRegion G a b, v.val = i := by
    intro i hi
    simp only [r,Nat.testBit_and,Bool.and_eq_true,Nat.testBit_or,Bool.or_eq_true] at hi
    have hia : i ≠ a.val := by
      intro h
      subst i
      simpa [mask,bit_eq_pow,Nat.testBit_xor,Nat.testBit_two_pow,Nat.testBit_two_pow_sub_one,
        a.isLt,hne.symm] using hi.2
    have hib : i ≠ b.val := by
      intro h
      subst i
      simpa [mask,bit_eq_pow,Nat.testBit_xor,Nat.testBit_two_pow,Nat.testBit_two_pow_sub_one,
        b.isLt,hne] using hi.2
    have hv : ∃ v : Fin n, v.val = i ∧ (G.Adj a v ∨ G.Adj b v) := by
      rcases hi.1 with ha | hb
      · have ha' : adjacent n (encodeGraph G) a.val i = true := by
          simpa only [adjacent,bne_iff_ne,band_bit_nonzero] using ha
        obtain ⟨u,v,hu,hv,huv⟩ := (encoded_adj_iff G a.val i).mp ha'
        have hua : u = a := Fin.ext hu
        subst u
        exact ⟨v,hv,Or.inl huv⟩
      · have hb' : adjacent n (encodeGraph G) b.val i = true := by
          simpa only [adjacent,bne_iff_ne,band_bit_nonzero] using hb
        obtain ⟨u,v,hu,hv,huv⟩ := (encoded_adj_iff G b.val i).mp hb'
        have hub : u = b := Fin.ext hu
        subst u
        exact ⟨v,hv,Or.inr huv⟩
    obtain ⟨v,hvi,hv⟩ := hv
    refine ⟨v,(mem_endpointRegion G a b v).mpr ⟨hv,?_,?_⟩,hvi⟩
    · intro h; subst v; exact hia hvi.symm
    · intro h; subst v; exact hib hvi.symm
  have hint := internal_le_sum_lower G r (endpointRegion G a b) hr
  rw [sum_lowerNeighbours] at hint
  have hcom := encoded_common_le G a b
  simp only [low,Bool.and_eq_true,decide_eq_true_eq]
  change _ ≤ _ at hint
  dsimp only [r] at hint
  omega

noncomputable def selectedPairs {n : Nat} (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) :
    Finset Edge :=
  ((univ ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 < p.2 ∧
    ∃ h : G.Adj p.1 p.2, (⟨s(p.1,p.2),h⟩ : G.edgeSet) ∈ Q)).image
    (fun p => (p.1.val,p.2.val))

theorem mem_selectedPairs {n : Nat} (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) (e : Edge) :
    e ∈ selectedPairs G Q ↔ ∃ a b : Fin n, (a.val,b.val) = e ∧ a < b ∧
      ∃ h : G.Adj a b, (⟨s(a,b),h⟩ : G.edgeSet) ∈ Q := by
  simp only [selectedPairs,mem_image,mem_filter,mem_product,mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨a,b,⟨hab,hq⟩,he⟩
    exact ⟨a,b,he,hab,hq⟩
  · rintro ⟨a,b,he,hab,hq⟩
    exact ⟨a,b,⟨hab,hq⟩,he⟩

noncomputable def encodeSelected {n : Nat} (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) :
    State := ⟨encodeGraph G,(selectedPairs G Q).toList⟩

theorem selectedPairs_card {n : Nat} (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) :
    (selectedPairs G Q).card = Q.card := by
  have hinj : Function.Injective (fun p : Fin n × Fin n => (p.1.val,p.2.val)) := by
    intro p q h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact Fin.ext (congrArg Prod.snd h)
  rw [selectedPairs,card_image_of_injective _ hinj]
  apply card_bij (fun p hp =>
    (⟨s(p.1,p.2),((mem_filter.mp hp).2.2).choose⟩ : G.edgeSet))
  · intro p hp
    exact ((mem_filter.mp hp).2.2).choose_spec
  · intro p hp q hq heq
    have hp' := (mem_filter.mp hp).2.1
    have hq' := (mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp (congrArg Subtype.val heq) with he | he
    · exact Prod.ext he.1 he.2
    · rw [he.1,he.2] at hp'
      exact False.elim (lt_asymm hp' hq')
  · rintro ⟨e,heG⟩ heQ
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := heG
      rcases lt_or_gt_of_ne hab.ne with hlt | hgt
      · exact ⟨(a,b),mem_filter.mpr ⟨by simp,hlt,hab,heQ⟩,rfl⟩
      · have hswap : (⟨s(b,a),hab.symm⟩ : G.edgeSet) = ⟨s(a,b),hab⟩ :=
          Subtype.ext Sym2.eq_swap
        exact ⟨(b,a),mem_filter.mpr ⟨by simp,hgt,hab.symm,hswap.symm ▸ heQ⟩,hswap⟩

theorem encodeSelected_length {n : Nat} (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) :
    (encodeSelected G Q).chosen.length = Q.card := by
  simp only [encodeSelected,Finset.length_toList,selectedPairs_card]

theorem encodeSelected_model {n : Nat} (G : SimpleGraph (Fin n))
    (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hLow : DReduction.LocallyLow G Q) :
    Model n (encodeSelected G Q) := by
  have hmem (e : Edge) : e ∈ (encodeSelected G Q).chosen ↔ e ∈ selectedPairs G Q := by
    simp [encodeSelected]
  constructor
  · simp only [valid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
    constructor
    · intro a ha
      have ha' : a < n := List.mem_range.mp ha
      exact (encoded_degree_le G ⟨a,ha'⟩).trans (hΔ ⟨a,ha'⟩)
    · intro e he
      obtain ⟨a,b,rfl,_,hab,heQ⟩ := (mem_selectedPairs G Q e).mp ((hmem e).mp he)
      exact encoded_low G a b hab (hLow a b hab heQ)
  · intro e he
    obtain ⟨a,b,rfl,_,_,_⟩ := (mem_selectedPairs G Q e).mp ((hmem e).mp he)
    exact ⟨a.isLt,b.isLt⟩
  · intro e he
    obtain ⟨a,b,rfl,_,hab,_⟩ := (mem_selectedPairs G Q e).mp ((hmem e).mp he)
    exact (encoded_adj G a b).mpr hab
  · exact encoded_symm G
  · exact encoded_irrefl G
  · intro e he f hf
    obtain ⟨a,b,rfl,_,hab,heQ⟩ := (mem_selectedPairs G Q e).mp ((hmem e).mp he)
    obtain ⟨c,d,rfl,_,hcd,hfQ⟩ := (mem_selectedPairs G Q f).mp ((hmem f).mp hf)
    apply (conflict_iff n (encodeGraph G) _ _).mpr
    by_cases heq : (⟨s(a,b),hab⟩ : G.edgeSet) = ⟨s(c,d),hcd⟩
    · rcases Sym2.eq_iff.mp (congrArg Subtype.val heq) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
    · obtain ⟨_,u,hu,v,hv,huv⟩ := hQ _ heQ _ hfQ heq
      simp only [Sym2.mem_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      all_goals rcases huv with heq | ha
      all_goals try { subst_vars; simp }
      all_goals have he := (encoded_adj G _ _).mpr ha
      all_goals simp [he]

#print axioms encoded_common_le
#print axioms encodeSelected_model
end Se20Fractional.FourthPass.Encoding
