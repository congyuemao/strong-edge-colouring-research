import Se20Part.Definitions

namespace Se20Part

/-- The explicit S11/S18 graph: 0,1,2,3,4 are p,q,a,b,c;
5,6 and 7,8 are U_p,U_q; 9,10 and 11,12 are V_a,V_b. -/
def ThirteenKernel : SimpleGraph (Fin 13) where
  Adj a b := a ≠ b ∧
    ((a.val < 5 ∧ b.val < 5 ∧ a.val / 2 ≠ b.val / 2) ∨
     (5 ≤ a.val ∧ 5 ≤ b.val ∧ (a.val-5)/4 = (b.val-5)/4) ∨
     (a.val < 4 ∧ 5 ≤ b.val ∧ (b.val-5)/2 = a.val) ∨
     (b.val < 4 ∧ 5 ≤ a.val ∧ (a.val-5)/2 = b.val))
  symm := ⟨by intros a b h; aesop⟩
  loopless := ⟨by intro a; simp⟩

instance : DecidableRel ThirteenKernel.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _ ∨ _ ∨ _)))

/-- The full set of labelled independent k-subsets, not representatives
modulo a conjectured automorphism group. -/
def ThirteenIndependent (S : Finset (Fin 13)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ ThirteenKernel.Adj a b

instance : DecidablePred ThirteenIndependent := fun _ =>
  inferInstanceAs (Decidable (∀ a ∈ _, ∀ b ∈ _, ¬ ThirteenKernel.Adj a b))

def thirteenIndependentSets (k : ℕ) : Finset (Finset (Fin 13)) :=
  (Finset.univ.powersetCard k).filter ThirteenIndependent

def thirteenTripleType (S : Finset (Fin 13)) : Fin 3 :=
  if 4 ∈ S then 2 else if (S.filter (fun v => v.val < 5)).card = 2 then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- S18's exact labelled counts: eight of type I, thirty-two of type II,
sixteen of type III. This does not assert the orbit or rotation claims. -/
theorem thirteenKernel_triple_counts :
    (thirteenIndependentSets 3).card = 56 ∧
    ((thirteenIndependentSets 3).filter (fun S => thirteenTripleType S = 0)).card = 8 ∧
    ((thirteenIndependentSets 3).filter (fun S => thirteenTripleType S = 1)).card = 32 ∧
    ((thirteenIndependentSets 3).filter (fun S => thirteenTripleType S = 2)).card = 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem thirteenKernel_no_independent_four : thirteenIndependentSets 4 = ∅ := by
  decide +kernel

theorem thirteenKernel_independent_card_le_three (S : Finset (Fin 13))
    (hS : ThirteenIndependent S) : S.card ≤ 3 := by
  by_contra hn
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ S.card)
  have hTi : ThirteenIndependent T := fun a ha b hb => hS a (hTS ha) b (hTS hb)
  have hm : T ∈ thirteenIndependentSets 4 := by
    simp only [thirteenIndependentSets, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨hT,hTi⟩
  simpa only [thirteenKernel_no_independent_four, Finset.notMem_empty] using hm

theorem thirteenKernel_degrees : ∀ v,
    ThirteenKernel.degree v = if v.val < 4 then 5 else 4 := by
  decide +kernel

/-- Canonical representatives I, II and III from S18. -/
def thirteenOrbitRepresentative : Fin 3 → Finset (Fin 13) :=
  ![{0,1,9}, {0,7,9}, {4,5,9}]

/-- Explicit permutation witnesses, checked below rather than trusted. -/
def thirteenTriplePermutation : Fin 56 → Fin 13 → Fin 13 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,12],
    ![0,1,3,2,4,5,6,7,8,11,12,9,10],
    ![0,1,2,3,4,5,6,7,8,10,9,11,12],
    ![2,3,0,1,4,9,10,11,12,5,6,7,8],
    ![0,1,3,2,4,5,6,7,8,12,11,9,10],
    ![2,3,1,0,4,9,10,11,12,7,8,5,6],
    ![2,3,0,1,4,9,10,11,12,6,5,7,8],
    ![2,3,1,0,4,9,10,11,12,8,7,5,6],
    ![0,1,2,3,4,5,6,7,8,9,10,11,12],
    ![1,0,2,3,4,7,8,5,6,9,10,11,12],
    ![0,1,3,2,4,5,6,7,8,11,12,9,10],
    ![0,1,2,3,4,5,6,8,7,9,10,11,12],
    ![0,1,2,3,4,5,6,7,8,10,9,11,12],
    ![2,3,0,1,4,9,10,11,12,5,6,7,8],
    ![1,0,3,2,4,7,8,5,6,11,12,9,10],
    ![1,0,2,3,4,7,8,6,5,9,10,11,12],
    ![1,0,2,3,4,7,8,5,6,10,9,11,12],
    ![3,2,0,1,4,11,12,9,10,5,6,7,8],
    ![0,1,3,2,4,5,6,8,7,11,12,9,10],
    ![0,1,3,2,4,5,6,7,8,12,11,9,10],
    ![2,3,1,0,4,9,10,11,12,7,8,5,6],
    ![0,1,2,3,4,5,6,8,7,10,9,11,12],
    ![2,3,0,1,4,9,10,12,11,5,6,7,8],
    ![2,3,0,1,4,9,10,11,12,6,5,7,8],
    ![1,0,3,2,4,7,8,6,5,11,12,9,10],
    ![1,0,3,2,4,7,8,5,6,12,11,9,10],
    ![3,2,1,0,4,11,12,9,10,7,8,5,6],
    ![1,0,2,3,4,7,8,6,5,10,9,11,12],
    ![3,2,0,1,4,11,12,10,9,5,6,7,8],
    ![3,2,0,1,4,11,12,9,10,6,5,7,8],
    ![0,1,3,2,4,5,6,8,7,12,11,9,10],
    ![2,3,1,0,4,9,10,12,11,7,8,5,6],
    ![2,3,1,0,4,9,10,11,12,8,7,5,6],
    ![2,3,0,1,4,9,10,12,11,6,5,7,8],
    ![1,0,3,2,4,7,8,6,5,12,11,9,10],
    ![3,2,1,0,4,11,12,10,9,7,8,5,6],
    ![3,2,1,0,4,11,12,9,10,8,7,5,6],
    ![3,2,0,1,4,11,12,10,9,6,5,7,8],
    ![2,3,1,0,4,9,10,12,11,8,7,5,6],
    ![3,2,1,0,4,11,12,10,9,8,7,5,6],
    ![0,1,2,3,4,5,6,7,8,9,10,11,12],
    ![1,0,2,3,4,7,8,5,6,9,10,11,12],
    ![0,1,3,2,4,5,6,7,8,11,12,9,10],
    ![0,1,2,3,4,6,5,7,8,9,10,11,12],
    ![0,1,2,3,4,5,6,7,8,10,9,11,12],
    ![1,0,3,2,4,7,8,5,6,11,12,9,10],
    ![1,0,2,3,4,8,7,5,6,9,10,11,12],
    ![1,0,2,3,4,7,8,5,6,10,9,11,12],
    ![0,1,3,2,4,6,5,7,8,11,12,9,10],
    ![0,1,3,2,4,5,6,7,8,12,11,9,10],
    ![0,1,2,3,4,6,5,7,8,10,9,11,12],
    ![1,0,3,2,4,8,7,5,6,11,12,9,10],
    ![1,0,3,2,4,7,8,5,6,12,11,9,10],
    ![1,0,2,3,4,8,7,5,6,10,9,11,12],
    ![0,1,3,2,4,6,5,7,8,12,11,9,10],
    ![1,0,3,2,4,8,7,5,6,12,11,9,10]]

def thirteenTripleOrbit : Fin 56 → Fin 3 :=
  ![0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]

def thirteenOrbitSet (i : Fin 56) : Finset (Fin 13) :=
  (thirteenOrbitRepresentative (thirteenTripleOrbit i)).image (thirteenTriplePermutation i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem thirteenKernel_permutations_valid : ∀ i,
    Function.Bijective (thirteenTriplePermutation i) ∧
    ∀ a b, ThirteenKernel.Adj (thirteenTriplePermutation i a) (thirteenTriplePermutation i b) ↔
      ThirteenKernel.Adj a b := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem thirteenKernel_triple_coverage :
    thirteenIndependentSets 3 = Finset.univ.image thirteenOrbitSet := by
  decide +kernel

noncomputable def thirteenKernelTripleIso (i : Fin 56) : ThirteenKernel ≃g ThirteenKernel where
  toEquiv := Equiv.ofBijective (thirteenTriplePermutation i) (thirteenKernel_permutations_valid i).1
  map_rel_iff' := fun {a b} => (thirteenKernel_permutations_valid i).2 a b

/-- Every independent triple is an automorphic image of one of the three
specified representatives. Coverage includes all labelled triples. -/
theorem thirteenKernel_triple_normal_form (S : Finset (Fin 13))
    (hS : S ∈ thirteenIndependentSets 3) :
    ∃ k : Fin 3, ∃ f : ThirteenKernel ≃g ThirteenKernel,
      S = (thirteenOrbitRepresentative k).image f := by
  rw [thirteenKernel_triple_coverage] at hS
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hS
  exact ⟨thirteenTripleOrbit i,thirteenKernelTripleIso i,hi.symm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem thirteenKernel_witness_type : ∀ i,
    thirteenTripleType (thirteenOrbitSet i) = thirteenTripleOrbit i := by
  decide +kernel

/-- The labelled types counted in S18 are exactly the automorphism classes. -/
theorem thirteenKernel_triple_normal_form_of_type (S : Finset (Fin 13))
    (hS : S ∈ thirteenIndependentSets 3) :
    ∃ f : ThirteenKernel ≃g ThirteenKernel,
      S = (thirteenOrbitRepresentative (thirteenTripleType S)).image f := by
  rw [thirteenKernel_triple_coverage] at hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  rw [thirteenKernel_witness_type]
  exact ⟨thirteenKernelTripleIso i,rfl⟩

theorem thirteenKernelIso_high (f : ThirteenKernel ≃g ThirteenKernel) (v : Fin 13) :
    (f v).val < 4 ↔ v.val < 4 := by
  have hd := f.degree_eq v
  rw [thirteenKernel_degrees,thirteenKernel_degrees] at hd
  split_ifs at hd <;> omega

theorem thirteenKernel_high_count_image (f : ThirteenKernel ≃g ThirteenKernel)
    (S : Finset (Fin 13)) :
    ((S.image f).filter (fun v => v.val < 4)).card = (S.filter (fun v => v.val < 4)).card := by
  have heq : (S.image f).filter (fun v => v.val < 4) =
      (S.filter (fun v => v.val < 4)).image f := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨w,hw,rfl⟩,hp⟩
      exact ⟨w,⟨hw,(thirteenKernelIso_high f w).mp hp⟩,rfl⟩
    · rintro ⟨w,⟨hw,hp⟩,rfl⟩
      exact ⟨⟨w,hw,rfl⟩,(thirteenKernelIso_high f w).mpr hp⟩
  rw [heq, Finset.card_image_of_injective _ f.injective]

theorem thirteenKernel_representative_high_count : ∀ k : Fin 3,
    ((thirteenOrbitRepresentative k).filter (fun v => v.val < 4)).card = 2 - k.val := by
  decide +kernel

/-- The three normal forms are in distinct orbits: their numbers of degree
five vertices are respectively two, one and zero. -/
theorem thirteenKernel_representatives_distinct (i j : Fin 3)
    (f : ThirteenKernel ≃g ThirteenKernel)
    (h : (thirteenOrbitRepresentative i).image f = thirteenOrbitRepresentative j) : i = j := by
  have hc := thirteenKernel_high_count_image f (thirteenOrbitRepresentative i)
  rw [h,thirteenKernel_representative_high_count,thirteenKernel_representative_high_count] at hc
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

end Se20Part
