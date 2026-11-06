import fourth_pass.ProfileEnumeration

namespace Se20Fractional.FourthPass.Packed
def rootAllowed (d s m : Nat) : Bool :=
  valid 14 ⟨profileGraph d m [],rootChosen s⟩ &&
    (innerEdges d m).all (fun e => decide (s < e.2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allowed33 : ∀ m : Fin 8, rootAllowed 3 3 m = true → m.val = 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allowed43 : ∀ m : Fin 64, rootAllowed 4 3 m = true →
    m.val = 0 ∨ m.val = 4 ∨ m.val = 16 ∨ m.val = 32 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allowed44 : ∀ m : Fin 64, rootAllowed 4 4 m = true → m.val = 0 := by decide +kernel
end Se20Fractional.FourthPass.Packed

namespace Se20Fractional.FourthPass.Canonical
open Finset ThirdPass Encoding Packed
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem Listing.types_sorted {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : L.types.Pairwise (· ≤ ·) := by
  exact List.pairwise_map.mpr L.U_sorted

theorem Listing.types_bounded {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : ∀ t ∈ L.types, t < 2^(G.degree r) := by
  intro t ht
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ht
  simpa only [L.A_length] using typeMask_lt G r L.A x

theorem Listing.innerCode_lt {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : L.innerCode < 2^(innerPairs (G.degree r)).length :=
  predicateCode_lt _ _

theorem Listing.root_allowed {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (hΔ : ∀ v, G.degree v ≤ 4) (hQ : Clique (L2 G) Q)
    (hLow : DReduction.LocallyLow G Q) (hsize : Q.card = 16)
    (hs : 3 ≤ (labels Q r).card) :
    rootAllowed (G.degree r) (labels Q r).card L.innerCode = true := by
  let P := L.profile hΔ hQ hLow hsize hs
  have hlabel (v : Fin 14) (hv : 1 ≤ v.val) (hvs : v.val ≤ (labels Q r).card) :
      L.equiv v ∈ labels Q r := by
    have hi : v.val-1 < L.A.length := by have := P.s_le; rw [L.A_length]; omega
    have he : L.equiv v = L.A[v.val-1] := by
      have heq : v = ⟨v.val-1+1,by omega⟩ := Fin.ext (by simp; omega)
      exact (congrArg L.equiv heq).trans (L.equiv_A _ hi)
    rw [he]
    exact (L.A_label_iff _ hi).mpr (by omega)
  simp only [rootAllowed,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  constructor
  · exact P.prefix_valid (as := []) (bs := L.types)
  · intro e he
    have hb := mem_innerEdges_bounds he
    by_contra hn
    have has : e.1 ≤ (labels Q r).card := by omega
    have hbs : e.2 ≤ (labels Q r).card := by omega
    have ha14 : e.1 < 14 := by have := hΔ r; omega
    have hb14 : e.2 < 14 := by have := hΔ r; omega
    have hed := (P.inner e.1 e.2 hb.1 hb.2.1 hb.2.2).mp he
    have hed' : G.Adj (L.equiv ⟨e.1,ha14⟩) (L.equiv ⟨e.2,hb14⟩) := by
      exact (L.graph_adj _ _).mp ((encoded_adj L.graph ⟨e.1,ha14⟩ ⟨e.2,hb14⟩).mp hed)
    exact selected_labels_independent hΔ Q hQ hLow (by omega) hs
      (hlabel ⟨e.1,ha14⟩ hb.1 has) (hlabel ⟨e.2,hb14⟩ (by dsimp; omega) hbs) hed'

#print axioms Listing.root_allowed

theorem no_obstruction_of_six
    (h33 : CompletionFree 3 3 0 [] 0 10)
    (h430 : CompletionFree 4 3 0 [] 0 9)
    (h434 : CompletionFree 4 3 4 [] 0 9)
    (h4316 : CompletionFree 4 3 16 [] 0 9)
    (h4332 : CompletionFree 4 3 32 [] 0 9)
    (h44 : CompletionFree 4 4 0 [] 0 9) :
    ∀ G : SimpleGraph (Fin 14), ∀ Q : Finset G.edgeSet, ¬ Obstruction14 G Q := by
  intro G Q h
  obtain ⟨hΔ,hsize,hQ,hLow,_⟩ := h
  obtain ⟨r,hs⟩ := exists_three_labels hΔ Q hQ (by omega)
  obtain ⟨L⟩ := exists_listing G Q r
  have P := L.profile hΔ hQ hLow hsize hs
  have hallowed := L.root_allowed hΔ hQ hLow hsize hs
  have hm := L.innerCode_lt
  have hsorted := L.types_sorted
  have hbounded := L.types_bounded
  have hd := hΔ r
  have hsd := P.s_le
  have hcases : (G.degree r = 3 ∧ (labels Q r).card = 3) ∨
      (G.degree r = 4 ∧ (labels Q r).card = 3) ∨
      (G.degree r = 4 ∧ (labels Q r).card = 4) := by omega
  rcases hcases with ⟨hd,hs⟩ | ⟨hd,hs⟩ | ⟨hd,hs⟩
  · rw [hd,hs] at P hallowed
    rw [hd] at hm hbounded
    have hm8 : L.innerCode < 8 := hm
    have hm0 := allowed33 ⟨L.innerCode,hm8⟩ hallowed
    change L.innerCode = 0 at hm0
    rw [hm0] at P
    exact h33 L.types (by have := P.length; omega) hsorted
      (fun t ht => ⟨Nat.zero_le _,hbounded t ht⟩) _ P
  · rw [hd,hs] at P hallowed
    rw [hd] at hm hbounded
    have hm64 : L.innerCode < 64 := hm
    have hmc := allowed43 ⟨L.innerCode,hm64⟩ hallowed
    change L.innerCode = 0 ∨ L.innerCode = 4 ∨ L.innerCode = 16 ∨ L.innerCode = 32 at hmc
    have hl : L.types.length = 9 := by have := P.length; omega
    have hb : ∀ t ∈ L.types, 0 ≤ t ∧ t < 2^4 := fun t ht => ⟨Nat.zero_le _,hbounded t ht⟩
    rcases hmc with hm0 | hm4 | hm16 | hm32
    · rw [hm0] at P; exact h430 L.types hl hsorted hb _ P
    · rw [hm4] at P; exact h434 L.types hl hsorted hb _ P
    · rw [hm16] at P; exact h4316 L.types hl hsorted hb _ P
    · rw [hm32] at P; exact h4332 L.types hl hsorted hb _ P
  · rw [hd,hs] at P hallowed
    rw [hd] at hm hbounded
    have hm64 : L.innerCode < 64 := hm
    have hm0 := allowed44 ⟨L.innerCode,hm64⟩ hallowed
    change L.innerCode = 0 at hm0
    rw [hm0] at P
    exact h44 L.types (by have := P.length; omega) hsorted
      (fun t ht => ⟨Nat.zero_le _,hbounded t ht⟩) _ P

#print axioms no_obstruction_of_six
end Se20Fractional.FourthPass.Canonical
