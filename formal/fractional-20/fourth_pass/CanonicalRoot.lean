import fourth_pass.GraphEncoding
import Mathlib.Data.List.NodupEquivFin

namespace Se20Fractional.FourthPass.Canonical
open Finset ThirdPass Encoding
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def typeMask {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A : List V) (x : V) : Nat :=
  Finset.equivBitIndices.symm ((range A.length).filter (fun i => G.Adj x (A[i]?.getD r)))

theorem typeMask_bit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A : List V) (x : V) (i : Nat) :
    (typeMask G r A x).testBit i = true ↔ i < A.length ∧ G.Adj x (A[i]?.getD r) := by
  have he := Finset.equivBitIndices.apply_symm_apply
    ((range A.length).filter (fun i => G.Adj x (A[i]?.getD r)))
  change (typeMask G r A x).bitIndices.toFinset = _ at he
  have hmem := Finset.ext_iff.mp he i
  simpa using hmem

theorem typeMask_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A : List V) (x : V) :
    typeMask G r A x < 2^A.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hb
  have := ((typeMask_bit G r A x i).mp hb).1
  omega

structure Listing (G : SimpleGraph (Fin 14)) (Q : Finset G.edgeSet) (r : Fin 14) where
  A : List (Fin 14)
  U : List (Fin 14)
  A_length : A.length = G.degree r
  A_mem : ∀ x, x ∈ A ↔ G.Adj r x
  A_selected : A.take (labels Q r).card = (labels Q r).toList
  U_mem : ∀ x, x ∈ U ↔ x ≠ r ∧ ¬ G.Adj r x
  U_sorted : U.Pairwise (fun x y => typeMask G r A x ≤ typeMask G r A y)
  nodup : (r :: (A ++ U)).Nodup
  length : (r :: (A ++ U)).length = 14
  complete : ∀ x, x ∈ r :: (A ++ U)

theorem exists_listing (G : SimpleGraph (Fin 14)) (Q : Finset G.edgeSet) (r : Fin 14) :
    Nonempty (Listing G Q r) := by
  let S := labels Q r
  let B := G.neighborFinset r \ S
  let A := S.toList ++ B.toList
  let W := (univ : Finset (Fin 14)) \ insert r (G.neighborFinset r)
  let U := W.toList.mergeSort (fun x y => typeMask G r A x ≤ typeMask G r A y)
  have hSm (x : Fin 14) (hx : x ∈ S) : G.Adj r x := by
    exact (mem_labels Q r x).mp hx |>.choose
  have hAm (x : Fin 14) : x ∈ A ↔ G.Adj r x := by
    simp only [A,List.mem_append,mem_toList,B,mem_sdiff]
    constructor
    · rintro (h | ⟨h,_⟩)
      · exact hSm x h
      · simpa using h
    · intro h
      by_cases hx : x ∈ S
      · exact Or.inl hx
      · exact Or.inr ⟨by simpa using h,hx⟩
  have hWm (x : Fin 14) : x ∈ W ↔ x ≠ r ∧ ¬ G.Adj r x := by
    simp [W,not_or]
  have hUm (x : Fin 14) : x ∈ U ↔ x ≠ r ∧ ¬ G.Adj r x := by
    simpa [U] using hWm x
  have hAn : A.Nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_toList _,nodup_toList _,?_⟩
    intro x hx y hy heq
    subst y
    exact (mem_sdiff.mp (mem_toList.mp hy)).2 (mem_toList.mp hx)
  have hUn : U.Nodup := (List.mergeSort_perm W.toList _).nodup_iff.mpr (nodup_toList W)
  have hAU : (A ++ U).Nodup := by
    rw [List.nodup_append]
    refine ⟨hAn,hUn,?_⟩
    intro x hx y hy heq
    subst y
    exact ((hUm x).mp hy).2 ((hAm x).mp hx)
  have hL : (r :: (A ++ U)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hAU⟩
    simp only [List.mem_append,hAm,hUm,not_and,not_or]
    simp
  have hall (x : Fin 14) : x ∈ r :: (A ++ U) := by
    by_cases hxr : x = r
    · simp [hxr]
    by_cases hx : G.Adj r x
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((hAm x).mpr hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ ((hUm x).mpr ⟨hxr,hx⟩))
  have hlen : (r :: (A ++ U)).length = 14 := by
    have he : (r :: (A ++ U)).toFinset = univ := by
      ext x
      simpa only [List.mem_toFinset,mem_univ,iff_true] using hall x
    have hc := List.toFinset_card_of_nodup hL
    rw [he] at hc
    simpa using hc.symm
  have hAlen : A.length = G.degree r := by
    have he : A.toFinset = G.neighborFinset r := by ext x; simp [hAm]
    have hc := List.toFinset_card_of_nodup hAn
    rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc.symm
  refine ⟨⟨A,U,hAlen,hAm,?_,hUm,?_,hL,hlen,hall⟩⟩
  · change (S.toList ++ B.toList).take S.card = S.toList
    rw [← length_toList S,List.take_left]
  · simpa only [U,decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun x y => decide (typeMask G r A x ≤ typeMask G r A y))
        (by
          intro a b c hab hbc
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact Nat.le_trans hab hbc)
        (by
          intro a b
          simp only [Bool.or_eq_true,decide_eq_true_eq]
          exact Nat.le_total _ _) W.toList)

noncomputable def Listing.equiv {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : Fin 14 ≃ Fin 14 :=
  (finCongr L.length.symm).trans
    (L.nodup.getEquivOfForallMemList (r :: (L.A ++ L.U)) L.complete)

theorem Listing.equiv_zero {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : L.equiv 0 = r := rfl

theorem Listing.equiv_A {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (i : Nat) (hi : i < L.A.length) :
    L.equiv ⟨i+1,by have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩ =
      L.A[i] := by
  change (L.A ++ L.U)[i]'(by simp only [List.length_append]; omega) = L.A[i]
  exact List.getElem_append_left hi

theorem Listing.equiv_U {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (i : Nat) (hi : i < L.U.length) :
    L.equiv ⟨L.A.length+1+i,by
      have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩ = L.U[i] := by
  have he : L.A.length+1+i = (L.A.length+i)+1 := by omega
  simp only [Listing.equiv,Equiv.trans_apply,finCongr_apply_mk,
    List.Nodup.getEquivOfForallMemList_apply,List.get_eq_getElem]
  simp [he,List.getElem_append_right (Nat.le_add_right _ _)]

theorem Listing.A_nodup {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : L.A.Nodup :=
  (List.nodup_append.mp (List.nodup_cons.mp L.nodup).2).1

theorem Listing.A_label_iff {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (i : Nat) (hi : i < L.A.length) :
    L.A[i] ∈ labels Q r ↔ i < (labels Q r).card := by
  rw [← mem_toList,← L.A_selected]
  rw [List.mem_take_iff_idxOf_lt (List.getElem_mem hi)]
  simp [L.A_nodup.idxOf_getElem]

theorem Listing.root_adj_iff {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (v : Fin 14) :
    G.Adj r (L.equiv v) ↔ 0 < v.val ∧ v.val ≤ G.degree r := by
  by_cases hv : v.val = 0
  · have he : v = 0 := Fin.ext hv
    simp [he,L.equiv_zero]
  by_cases hA : v.val ≤ L.A.length
  · have hi : v.val-1 < L.A.length := by omega
    have he : v = (⟨(v.val-1)+1,by
        have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩ : Fin 14) :=
      Fin.ext (by change v.val = (v.val-1)+1; omega)
    rw [he,L.equiv_A _ hi]
    have ha := (L.A_mem _).mp (List.getElem_mem hi)
    simp only [ha,true_iff]
    rw [← L.A_length]
    omega
  · have hi : v.val-(L.A.length+1) < L.U.length := by
      have := L.length
      simp only [List.length_cons,List.length_append] at this
      omega
    have he : v = (⟨L.A.length+1+(v.val-(L.A.length+1)),by
        have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩ : Fin 14) :=
      Fin.ext (by change v.val = L.A.length+1+(v.val-(L.A.length+1)); omega)
    have hnot : ¬ G.Adj r (L.equiv v) := by
      rw [he,L.equiv_U _ hi]
      exact ((L.U_mem _).mp (List.getElem_mem hi)).2
    simp only [hnot,false_iff,not_and]
    rw [← L.A_length]
    omega

#print axioms exists_listing
end Se20Fractional.FourthPass.Canonical
