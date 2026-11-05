import Se20Insertion.ComponentInsertion

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Se20Insertion

/-- Summing an unordered pair contribution incident to one specified colour. -/
theorem sum_pair_star (p : Colour) (t : Colour → ℤ) (ht : t p = 0) :
    (∑ a : Colour, ∑ b : Colour, if a < b then
      (if a = p then t b else if b = p then t a else 0) else 0) = ∑ x : Colour, t x := by
  have heq (a b : Colour) : (if a < b then (if a = p then t b else if b = p then t a else 0) else 0) =
      (if a = p then if p < b then t b else 0 else 0) +
      (if b = p then if a < p then t a else 0 else 0) := by
    by_cases ha : a = p <;> by_cases hb : b = p <;> by_cases hab : a < b <;> simp_all
  simp_rw [heq,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases lt_trichotomy p x with h | h | h <;> simp_all [not_lt_of_ge,le_of_lt]

theorem sum_pair_two_stars (p q : Colour) (hpq : p ≠ q) (d : Colour → Colour → ℤ)
    (hsym : ∀ a b, d a b = d b a) (hpq0 : d p q = 0)
    (hzero : ∀ a b, a ≠ p → a ≠ q → b ≠ p → b ≠ q → d a b = 0) :
    (∑ a : Colour, ∑ b : Colour, if a < b then d a b else 0) =
      ∑ x ∈ (Finset.univ \ {p,q}), (d p x + d q x) := by
  let tp := fun x => if x = p ∨ x = q then 0 else d p x
  let tq := fun x => if x = p ∨ x = q then 0 else d q x
  have hqp0 : d q p = 0 := (hsym q p).trans hpq0
  have heq (a b : Colour) (hab : a ≠ b) : d a b =
      (if a = p then tp b else if b = p then tp a else 0) +
      (if a = q then tq b else if b = q then tq a else 0) := by
    by_cases hap : a = p <;> by_cases haq : a = q <;>
      by_cases hbp : b = p <;> by_cases hbq : b = q <;>
      simp_all [tp,tq,hsym,hzero]
  have hs : (∑ a : Colour, ∑ b : Colour, if a < b then d a b else 0) =
      (∑ a : Colour, ∑ b : Colour, if a < b then (if a = p then tp b else if b = p then tp a else 0) else 0) +
      (∑ a : Colour, ∑ b : Colour, if a < b then (if a = q then tq b else if b = q then tq a else 0) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    by_cases hab : a < b
    · simp [hab,heq a b (ne_of_lt hab)]
    · simp [hab]
  rw [hs,sum_pair_star p tp (by simp [tp]),sum_pair_star q tq (by simp [tq])]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.sdiff_eq_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = p ∨ x = q <;> simp [tp,tq,hx,Finset.mem_insert,Finset.mem_singleton]

namespace PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

def pairVertices (φ : PartialColouring H F) (a b : Colour) : Finset W :=
  F.filter (fun x => φ.colour x = a ∨ φ.colour x = b)

def pairComponents (φ : PartialColouring H F) (a b : Colour) : ℤ :=
  ComponentInsertion.count H (φ.pairVertices a b)

theorem pairComponents_eq (φ : PartialColouring H F) (a b : Colour) :
    φ.pairComponents a b = Nat.card (φ.KempeGraph a b).ConnectedComponent := by
  have heq : (↑(φ.pairVertices a b) : Set W) = φ.Bicoloured a b := by
    ext x; simp [pairVertices,Bicoloured]
  unfold pairComponents ComponentInsertion.count
  rw [heq]; rfl

theorem componentCount_sum (φ : PartialColouring H F) :
    (φ.componentCount : ℤ) = ∑ a : Colour, ∑ b : Colour, if a < b then φ.pairComponents a b else 0 := by
  simp only [componentCount,Nat.cast_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  by_cases h : a < b <;> simp only [h,ite_true,ite_false,pairComponents_eq,Nat.cast_zero]

theorem pairComponents_symm (φ : PartialColouring H F) (a b : Colour) :
    φ.pairComponents a b = φ.pairComponents b a := by
  have heq : φ.pairVertices a b = φ.pairVertices b a := by ext x; simp [pairVertices,or_comm]
  unfold pairComponents; rw [heq]

def recolourOne (φ : PartialColouring H F) (f : W) (b : Colour) (hb : φ.Free f b) : PartialColouring H F where
  colour x := if x = f then b else φ.colour x
  proper := by
    intro x y hx hy hxy heq
    by_cases hxf : x = f
    · subst x
      have hyf := hxy.ne.symm
      exact hb ⟨y,hy,hxy,by simpa [hyf] using heq.symm⟩
    by_cases hyf : y = f
    · subst y
      exact hb ⟨x,hx,hxy.symm,by simpa [hxf] using heq⟩
    exact φ.proper hx hy hxy (by simpa [hxf,hyf] using heq)

theorem recolour_gain (φ : PartialColouring H F) {f : W} (hf : f ∈ F)
    {p b : Colour} (hp : φ.colour f = p) (hbp : b ≠ p) (hb : φ.Free f b) :
    ((φ.recolourOne f b hb).componentCount : ℤ) - φ.componentCount =
      ∑ x ∈ (Finset.univ \ {p,b}),
        ((ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) f : ℤ) -
          ComponentInsertion.touchingCount H (φ.pairVertices b x) f) := by
  let ψ := φ.recolourOne f b hb
  let d := fun a c => ψ.pairComponents a c - φ.pairComponents a c
  have unchanged (a c : Colour) (ha : a ≠ p) (hab : a ≠ b) (hc : c ≠ p) (hcb : c ≠ b) :
      ψ.pairVertices a c = φ.pairVertices a c := by
    ext y
    by_cases hy : y = f <;> simp [ψ,recolourOne,pairVertices,hy,hp,ha.symm,hab.symm,hc.symm,hcb.symm]
  have both : ψ.pairVertices p b = φ.pairVertices p b := by
    ext y; by_cases hy : y = f <;> simp [ψ,recolourOne,pairVertices,hy,hp]
  have dsum : (ψ.componentCount : ℤ) - φ.componentCount =
      ∑ x ∈ (Finset.univ \ {p,b}), (d p x + d b x) := by
    rw [ψ.componentCount_sum,φ.componentCount_sum,← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hc : (∑ a : Colour, ∑ c : Colour, ((if a < c then ψ.pairComponents a c else 0) -
        (if a < c then φ.pairComponents a c else 0))) = ∑ a : Colour, ∑ c : Colour, if a < c then d a c else 0 := by
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro c _
      by_cases h : a < c <;> simp [h,d]
    rw [hc]
    exact sum_pair_two_stars p b hbp.symm d
      (fun a c => by dsimp [d]; rw [ψ.pairComponents_symm a c,φ.pairComponents_symm a c])
      (by simp [d,pairComponents,both])
      (fun a c ha hab hc hcb => by simp [d,pairComponents,unchanged a c ha hab hc hcb])
  rw [dsum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxp : x ≠ p := fun h => (Finset.mem_sdiff.mp hx).2 (by simp [h])
  have hxb : x ≠ b := fun h => (Finset.mem_sdiff.mp hx).2 (by simp [h])
  have he : ψ.pairVertices p x = (φ.pairVertices p x).erase f := by
    ext y; by_cases hy : y = f <;> simp [ψ,recolourOne,pairVertices,hy,hp,hbp,hxb.symm,and_assoc,and_left_comm]
  have hi : ψ.pairVertices b x = insert f (φ.pairVertices b x) := by
    ext y; by_cases hy : y = f <;> simp [ψ,recolourOne,pairVertices,hy,hp,hf]
  have hfpx : f ∈ φ.pairVertices p x := by simp [pairVertices,hf,hp]
  have hfbx : f ∉ φ.pairVertices b x := by simp [pairVertices,hp,hbp.symm,hxp.symm]
  have hd := ComponentInsertion.count_insert H ((φ.pairVertices p x).erase f) f (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hfpx] at hd
  have ha := ComponentInsertion.count_insert H (φ.pairVertices b x) f hfbx
  have hd' : (ComponentInsertion.count H (φ.pairVertices p x) : ℤ) +
      ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) f =
      ComponentInsertion.count H ((φ.pairVertices p x).erase f) + 1 := by exact_mod_cast hd
  have ha' : (ComponentInsertion.count H (insert f (φ.pairVertices b x)) : ℤ) +
      ComponentInsertion.touchingCount H (φ.pairVertices b x) f =
      ComponentInsertion.count H (φ.pairVertices b x) + 1 := by exact_mod_cast ha
  dsimp [d,pairComponents]
  rw [he,hi]
  omega

end PartialColouring
end Se20Insertion
