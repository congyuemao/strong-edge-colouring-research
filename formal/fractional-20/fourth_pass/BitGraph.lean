import fourth_pass.BitCount

namespace Se20Fractional.FourthPass.Packed

theorem BitSubset.refl (a : Nat) : BitSubset a a := fun _ h => h
theorem BitSubset.trans {a b c : Nat} (hab : BitSubset a b) (hbc : BitSubset b c) :
    BitSubset a c := fun i hi => hbc i (hab i hi)
theorem BitSubset.band {a b c d : Nat} (hab : BitSubset a b) (hcd : BitSubset c d) :
    BitSubset (a &&& c) (b &&& d) := by
  intro i hi
  simp only [Nat.testBit_and,Bool.and_eq_true] at hi ⊢
  exact ⟨hab i hi.1,hcd i hi.2⟩
theorem BitSubset.bor {a b c d : Nat} (hab : BitSubset a b) (hcd : BitSubset c d) :
    BitSubset (a ||| c) (b ||| d) := by
  intro i hi
  simp only [Nat.testBit_or,Bool.or_eq_true] at hi ⊢
  exact hi.elim (fun h => Or.inl (hab i h)) (fun h => Or.inr (hcd i h))
theorem BitSubset.shift {a b : Nat} (hab : BitSubset a b) (k : Nat) :
    BitSubset (a >>> k) (b >>> k) := by
  intro i hi
  simp only [Nat.testBit_shiftRight] at hi ⊢
  exact hab (k+i) hi
theorem row_mono {a b : Nat} (hab : BitSubset a b) (n i : Nat) :
    BitSubset (row n a i) (row n b i) :=
  (hab.shift (n*i)).band (.refl _)

theorem bit_eq_pow (i : Nat) : bit i = 2^i := by simp [bit,Nat.shiftLeft_eq]
theorem band_bit_nonzero (x i : Nat) : (x &&& bit i) ≠ 0 ↔ x.testBit i = true := by
  rw [bit_eq_pow,Nat.and_two_pow]
  cases x.testBit i <;> simp [Nat.two_pow_pos]
theorem band_bit_zero (x i : Nat) : (x &&& bit i) = 0 ↔ x.testBit i = false := by
  rw [bit_eq_pow,Nat.and_two_pow]
  cases x.testBit i <;> simp [Nat.two_pow_pos]

theorem internal_mono (n : Nat) {h g r t : Nat}
    (hh : BitSubset h g) (hr : BitSubset r t) (k : Nat) :
    internal n h r k ≤ internal n g t k := by
  induction k with
  | zero => simp [internal]
  | succ k ih =>
    have hc := pop_mono (((row_mono hh n k).band hr).band (.refl (mask k))) n
    have hbit : (r &&& bit k) ≠ 0 → (t &&& bit k) ≠ 0 := by
      intro h
      exact (band_bit_nonzero t k).mpr (hr k ((band_bit_nonzero r k).mp h))
    simp only [internal,beq_iff_eq]
    split_ifs <;> omega

theorem low_mono (n : Nat) {h g : Nat} (hh : BitSubset h g) (e : Edge)
    (hl : low n g e = true) : low n h e = true := by
  have ha := row_mono hh n e.1
  have hb := row_mono hh n e.2
  have ht := pop_mono (ha.band hb) n
  have hr := (ha.bor hb).band (.refl (mask n ^^^ bit e.1 ^^^ bit e.2))
  have hi := internal_mono n hh hr n
  simp only [low,Bool.and_eq_true,decide_eq_true_eq] at hl ⊢
  omega

theorem valid_mono (n : Nat) {h g : Nat} (hh : BitSubset h g) {q p : List Edge}
    (hq : ∀ e ∈ q, e ∈ p) (hv : valid n ⟨g,p⟩ = true) : valid n ⟨h,q⟩ = true := by
  simp only [valid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hv ⊢
  constructor
  · intro a ha
    exact (pop_mono (row_mono hh n a) n).trans (hv.1 a ha)
  · intro e he
    exact low_mono n hh e (hv.2 e (hq e he))

theorem adjacent_iff (n h a b : Nat) :
    adjacent n h a b = true ↔ h.testBit (n*a+b) = true ∧ b < n := by
  simp only [adjacent,bne_iff_ne]
  rw [band_bit_nonzero]
  simp only [row,Nat.testBit_and,
    Nat.testBit_shiftRight,Bool.and_eq_true,mask,bit_eq_pow,Nat.testBit_two_pow_sub_one,
    decide_eq_true_eq]

theorem row_bitIndices_length_le (n h a : Nat) : (row n h a).bitIndices.length ≤ n := by
  have hs : (row n h a).bitIndices.toFinset ⊆ Finset.range n := by
    intro b hb
    simp only [List.mem_toFinset,Nat.mem_bitIndices] at hb
    simp only [row,Nat.testBit_and,Bool.and_eq_true,Nat.testBit_shiftRight,
      mask,bit_eq_pow,Nat.testBit_two_pow_sub_one,decide_eq_true_eq] at hb
    exact Finset.mem_range.mpr hb.2
  have hc := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup Nat.bitIndices_nodup,Finset.card_range] using hc

theorem pop_row_eq (n h a : Nat) : pop n (row n h a) = (row n h a).bitIndices.length := by
  rw [pop_eq_min,Nat.min_eq_right (row_bitIndices_length_le n h a)]

theorem row_degree_strict {n h g a b : Nat} (hh : BitSubset h g)
    (hgb : adjacent n g a b = true) (hhb : adjacent n h a b = false) :
    pop n (row n h a) < pop n (row n g a) := by
  have hbitg : (row n g a).testBit b = true := by
    exact (band_bit_nonzero _ _).mp (by simpa only [adjacent,bne_iff_ne] using hgb)
  have hbith : (row n h a).testBit b = false := by
    apply (band_bit_zero _ _).mp
    simpa only [adjacent,bne_eq_false_iff_eq] using hhb
  have hs : insert b (row n h a).bitIndices.toFinset ⊆ (row n g a).bitIndices.toFinset := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa using hbitg
    · simp only [List.mem_toFinset,Nat.mem_bitIndices] at hi ⊢
      exact row_mono hh n a i hi
  have hb : b ∉ (row n h a).bitIndices.toFinset := by simp [hbith]
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hb,
    List.toFinset_card_of_nodup Nat.bitIndices_nodup,
    List.toFinset_card_of_nodup Nat.bitIndices_nodup] at hc
  rw [pop_row_eq,pop_row_eq]
  omega

theorem addEdge_subset {n h g : Nat} {e : Edge} (hh : BitSubset h g)
    (he : adjacent n g e.1 e.2 = true) (her : adjacent n g e.2 e.1 = true) :
    BitSubset (addEdge n h e) g := by
  intro i hi
  simp only [addEdge,Nat.testBit_or,Bool.or_eq_true,bit_eq_pow,Nat.testBit_two_pow,
    decide_eq_true_eq] at hi
  rcases hi with (hi | rfl) | rfl
  · exact hh i hi
  · exact ((adjacent_iff n g e.1 e.2).mp he).1
  · exact ((adjacent_iff n g e.2 e.1).mp her).1

theorem subset_addEdge (n h : Nat) (e : Edge) : BitSubset h (addEdge n h e) := by
  intro i hi
  simp [addEdge,hi]

theorem adjacent_mono {h g : Nat} (hh : BitSubset h g) (n a b : Nat)
    (ha : adjacent n h a b = true) : adjacent n g a b = true := by
  rw [adjacent_iff] at ha ⊢
  exact ⟨hh _ ha.1,ha.2⟩

theorem conflict_iff (n h : Nat) (e f : Edge) : conflict n h e f = true ↔
    e.1 = f.1 ∨ e.2 = f.1 ∨ adjacent n h e.1 f.1 = true ∨ adjacent n h e.2 f.1 = true ∨
    e.1 = f.2 ∨ e.2 = f.2 ∨ adjacent n h e.1 f.2 = true ∨ adjacent n h e.2 f.2 = true := by
  simp only [conflict,bne_iff_ne,Nat.and_or_distrib_left]
  simp only [ne_eq,Nat.or_eq_zero_iff,not_and_or]
  simp only [band_bit_nonzero,Nat.testBit_or,Bool.or_eq_true]
  simp only [bit_eq_pow,Nat.testBit_two_pow,decide_eq_true_eq,or_assoc]
  simp only [adjacent,bne_iff_ne]
  simp only [band_bit_nonzero]

theorem pair_index_inj {n a b c d : Nat} (hb : b < n) (hd : d < n) :
    n*a+b = n*c+d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have he : b = d := by
      have hm := congrArg (fun k => k % n) h
      simpa [Nat.add_mod,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hd] using hm
    have hn : n ≠ 0 := by omega
    have hm : n*a = n*c := by omega
    exact ⟨Nat.eq_of_mul_eq_mul_left (by omega) hm,he⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem adjacent_addEdge {n h a b : Nat} {e : Edge} (ha : a < n) (hb : b < n)
    (he1 : e.1 < n) (he2 : e.2 < n) :
    adjacent n (addEdge n h e) a b = true ↔
      adjacent n h a b = true ∨ (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1) := by
  simp only [adjacent_iff,hb,and_true,addEdge,Nat.testBit_or,Bool.or_eq_true,
    bit_eq_pow,Nat.testBit_two_pow,decide_eq_true_eq]
  rw [pair_index_inj he2 hb,pair_index_inj he1 hb]
  simp only [eq_comm,or_assoc]

theorem addEdge_symm {n h : Nat} {e : Edge}
    (hs : ∀ a, a < n → ∀ b, b < n → adjacent n h a b = adjacent n h b a)
    (he1 : e.1 < n) (he2 : e.2 < n) :
    ∀ a, a < n → ∀ b, b < n →
      adjacent n (addEdge n h e) a b = adjacent n (addEdge n h e) b a := by
  intro a ha b hb
  apply Bool.eq_iff_iff.mpr
  simp only [adjacent_addEdge ha hb he1 he2,adjacent_addEdge hb ha he1 he2,hs a ha b hb]
  tauto

#print axioms valid_mono
end Se20Fractional.FourthPass.Packed
