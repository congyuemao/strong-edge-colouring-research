import Se20Part.SegmentCounting
import Se20Part.PatternProducts

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 2000000

abbrev Decoration {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (Y : Segment G n) (f : SpanningPattern n) (k : ℕ) :=
  ∀ i : RootPositions f k, projectedCandidates G Y.walk i.val.val (f i.val).val

def endpointFactor {n : ℕ} (i : Fin (n+1)) : ℕ :=
  (if i = 0 then 2 else 1) * (if i = Fin.last n then 2 else 1)

theorem endpointFactor_pos {n : ℕ} (i : Fin (n+1)) : 1 ≤ endpointFactor i := by
  unfold endpointFactor
  split_ifs <;> norm_num

theorem endpointFactor_prod (n : ℕ) : (∏ i : Fin (n+1), endpointFactor i) = 4 := by
  simp only [endpointFactor,prod_mul_distrib,Fintype.prod_ite_eq',show 2*2=4 by norm_num]

theorem endpointFactor_subprod {n : ℕ} (f : SpanningPattern n) (k : ℕ) :
    (∏ i : RootPositions f k, endpointFactor i.val) ≤ 4 := by
  calc
    _ = ∏ i ∈ univ.filter (fun i : Fin (n+1) => i.val ≠ k ∧ (f i).val ≠ 0), endpointFactor i :=
      (prod_subtype (p := fun i : Fin (n+1) => i.val ≠ k ∧ (f i).val ≠ 0) _ (by simp) _).symm
    _ ≤ ∏ i : Fin (n+1), endpointFactor i :=
      prod_le_prod_of_subset_of_one_le (filter_subset _ _) (fun i _ _ => endpointFactor_pos i)
    _ = 4 := endpointFactor_prod n

theorem decoration_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {n : ℕ} (hn : 0 < n) (Y : Segment G n)
    (f : SpanningPattern n) (k : ℕ) :
    Fintype.card (Decoration Y f k) ≤ 4 * ∏ i : RootPositions f k, 2*3^(f i.val).val := by
  have hpoint (i : RootPositions f k) :
      Fintype.card (projectedCandidates G Y.walk i.val.val (f i.val).val) ≤
        endpointFactor i.val * (2*3^(f i.val).val) := by
    have hc := projectedCandidates_card_explicit hd Y.walk Y.isPath (by rw [Y.length]; exact hn)
      i.val.val (f i.val).val (by rw [Y.length]; exact Nat.le_of_lt_succ i.val.isLt)
      (Nat.pos_of_ne_zero i.property.2)
    rw [Nat.card_eq_fintype_card,Y.length] at hc
    have he : positionBranches n i.val.val ≤ endpointFactor i.val * 2 := by
      have hi0 : i.val.val = 0 ↔ i.val = 0 :=
        ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
      have hin : i.val.val = n ↔ i.val = Fin.last n :=
        ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
      simp only [positionBranches,hi0,hin,endpointFactor]
      split_ifs <;> norm_num at * <;> tauto
    exact hc.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_right (3^(f i.val).val) he)
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ i : RootPositions f k, endpointFactor i.val * (2*3^(f i.val).val) := prod_le_prod (fun i _ => hpoint i)
    _ = (∏ i : RootPositions f k, endpointFactor i.val) * ∏ i : RootPositions f k, 2*3^(f i.val).val := prod_mul_distrib
    _ ≤ _ := Nat.mul_le_mul_right _ (endpointFactor_subprod f k)

abbrev EmbeddedPattern {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) (n k d : ℕ)
    (f : SpanningPattern n) := Σ Y : RootSegment G e n k d, Decoration Y.val f k

theorem embeddedPattern_weight {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {n : ℕ} (hn : 0 < n) (e : G.edgeSet) (k d : ℕ)
    (hk : k ≤ n) (f : SpanningPattern n) :
    (Fintype.card (EmbeddedPattern G e n k d f) : ℚ) * t5710^(Fintype.card (RootPositions f k)) ≤
      24*3^d*rootedPatternWeight k f := by
  have hc : Fintype.card (EmbeddedPattern G e n k d f) ≤
      (6*3^d*3^n) * (4*∏ i : RootPositions f k, 2*3^(f i.val).val) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _Y : RootSegment G e n k d, 4*∏ i : RootPositions f k, 2*3^(f i.val).val :=
        sum_le_sum (fun Y _ => decoration_card hd hn Y.val f k)
      _ = Fintype.card (RootSegment G e n k d) * (4*∏ i : RootPositions f k, 2*3^(f i.val).val) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (rootSegment_card hd e n k d hk)
  have hc' : (Fintype.card (EmbeddedPattern G e n k d f) : ℚ) ≤
      (6*3^d*3^n) * (4*∏ i : RootPositions f k, (2*3^(f i.val).val : ℚ)) := by exact_mod_cast hc
  have ht : 0 ≤ t5710 := by norm_num [t5710,beta5710]
  have hh := mul_le_mul_of_nonneg_right hc' (pow_nonneg ht (Fintype.card (RootPositions f k)))
  rw [rootedPatternWeight_eq hk,rootFactor_prod]
  convert hh using 1 <;> ring

end Se20Part
