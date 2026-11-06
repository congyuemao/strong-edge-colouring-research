import Se20Part.BadFamilies

noncomputable section
open scoped Classical BigOperators
open Finset SimpleGraph
namespace Se20Part
set_option maxHeartbeats 0

theorem familyWeight_root {X I : Type} [Fintype X] (part : X → I)
    (hsize : ∀ i, 5710 ≤ partSize part i) (S : Finset X)
    (hinj : Set.InjOn part (S : Set X)) {i : I} (hi : i ∈ S.image part) :
    familyWeight part (1203/1000) S ≤
      ((1203/1000 : ℝ) / partSize part i) * (t5710 : ℝ)^(S.card-1) := by
  have heq : (S.image part).card = S.card := card_image_of_injOn hinj
  have hprod : (∏ j ∈ (S.image part).erase i, (1203/1000 : ℝ)/partSize part j) ≤
      (t5710 : ℝ)^(S.card-1) := by
    calc
      _ ≤ ∏ _j ∈ (S.image part).erase i, (t5710 : ℝ) := by
        apply prod_le_prod₀
        · intro j _; positivity
        · intro j _
          have hs : (5710 : ℝ) ≤ partSize part j := by exact_mod_cast hsize j
          have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1203/1000)
            (by norm_num : (0 : ℝ) < 5710) hs
          convert hdiv using 1 <;> norm_num [t5710,beta5710]
      _ = _ := by rw [prod_const,card_erase_of_mem hi,heq]
  have hh := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (1203/1000 : ℝ)/partSize part i)
  rw [mul_prod_erase (S.image part) (fun j => (1203/1000 : ℝ)/partSize part j) hi] at hh
  exact hh

/-- Rooting at the unique member of a specified part removes one factor of t.
This is the per-part convolution bookkeeping, separated from the embedding count. -/
theorem per_part_of_rooted_count {X I B : Type} [Fintype X] [Fintype I] [Fintype B]
    (part : X → I) (hsize : ∀ i, 5710 ≤ partSize part i)
    (family : B → Finset X) (hinj : ∀ b, Set.InjOn part (family b : Set X))
    (C : ℝ)
    (hroot : ∀ e : X,
      (∑ b : B, if e ∈ family b then (t5710 : ℝ)^((family b).card-1) else 0) ≤ C)
    (i : I) :
    (∑ b ∈ univ.filter (fun b => i ∈ (family b).image part),
      familyWeight part (1203/1000) (family b)) ≤ (1203/1000 : ℝ)*C := by
  let α : ℝ := (1203/1000 : ℝ) / partSize part i
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have ht : 0 ≤ (t5710 : ℝ) := by norm_num [t5710,beta5710]
  have hpoint (b : B) :
      (if i ∈ (family b).image part then familyWeight part (1203/1000) (family b) else 0) ≤
      α * ∑ e : {e // part e = i}, if e.val ∈ family b then (t5710 : ℝ)^((family b).card-1) else 0 := by
    by_cases hi : i ∈ (family b).image part
    · rw [if_pos hi]
      obtain ⟨e,he,hei⟩ := mem_image.mp hi
      have hb := familyWeight_root part hsize (family b) (hinj b) hi
      have hone : (t5710 : ℝ)^((family b).card-1) ≤
          ∑ a : {e // part e = i}, if a.val ∈ family b then (t5710 : ℝ)^((family b).card-1) else 0 := by
        have hs := single_le_sum (s := univ)
          (f := fun a : {e // part e = i} => if a.val ∈ family b then (t5710 : ℝ)^((family b).card-1) else 0)
          (fun a _ => by split_ifs <;> positivity) (mem_univ (⟨e,hei⟩ : {e // part e = i}))
        simpa [he] using hs
      exact hb.trans (mul_le_mul_of_nonneg_left hone hα)
    · rw [if_neg hi]
      exact mul_nonneg hα (sum_nonneg (fun e _ => by split_ifs <;> positivity))
  have hs := sum_le_sum (fun b (_ : b ∈ univ) => hpoint b)
  rw [← Finset.sum_filter,← Finset.mul_sum,Finset.sum_comm] at hs
  have hroots : (∑ e : {e // part e = i},
      ∑ b : B, if e.val ∈ family b then (t5710 : ℝ)^((family b).card-1) else 0) ≤
      (partSize part i : ℝ)*C := by
    have hh := sum_le_sum (fun e (_ : e ∈ univ (α := {e // part e = i})) => hroot e.val)
    simpa [partSize] using hh
  have hh := hs.trans (mul_le_mul_of_nonneg_left hroots hα)
  have hpos : (0 : ℝ) < partSize part i := by
    have hs := hsize i
    exact_mod_cast (show 0 < partSize part i by omega)
  have he : α * ((partSize part i : ℝ)*C) = (1203/1000 : ℝ)*C := by
    dsimp [α]
    field_simp
  rw [he] at hh
  exact hh

def rootedChainCount {V I : Type} [Fintype V] (G : SimpleGraph V)
    (E : Set G.edgeSet) (part : E → I) (e : E) : ℝ :=
  ∑ b : ChainBad G E part, if e ∈ b.val then (t5710 : ℝ)^(b.val.card-1) else 0

theorem chain_per_part_of_rooted {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (E : Set G.edgeSet) (part : E → I)
    (hsize : ∀ i, 5710 ≤ partSize part i) (C : ℝ)
    (hroot : ∀ e, rootedChainCount G E part e ≤ C) (i : I) :
    (∑ b ∈ univ.filter (fun b : ChainBad G E part => i ∈ b.val.image part),
      familyWeight part (1203/1000) b.val) ≤ (1203/1000 : ℝ)*C :=
  per_part_of_rooted_count part hsize (fun b : ChainBad G E part => b.val)
    (fun b => b.property.2.1) C (fun e => by
      convert hroot e using 1
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> rfl) i

end Se20Part
