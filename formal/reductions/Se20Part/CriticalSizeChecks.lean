import Se20Part.Definitions

namespace Se20Part.CriticalSizeChecks

/-- dense_complement41 §6: the entire range 26,...,40, checked in the kernel. -/
theorem component_product_obstruction (n : ℕ) (hlo : 26 ≤ n) (hhi : n ≤ 40) :
    n < (42-n)*(2*n-49) := by
  interval_cases n <;> norm_num

/-- critical41_triangles §4: the lower end of the matching-decomposition
parameter cannot be 0,...,12. -/
theorem triangle_parameter_lower (a : ℕ) (ha : a ≤ 12) :
    38 < a + (a+2)*(27-2*a) := by
  interval_cases a <;> norm_num

theorem triangle_parameter_range (a : ℕ)
    (hl : a + (a+2)*(27-2*a) ≤ 38) (hu : 2*a+2 ≤ 38) :
    13 ≤ a ∧ a ≤ 18 := by
  have hn : ¬ a ≤ 12 := fun h => (Nat.not_lt_of_ge hl) (triangle_parameter_lower a h)
  omega

/-- critical41_triangles §7: all three residual nontrivial-block cases. -/
theorem nontrivial_block_obstruction (a t : ℕ)
    (hc : (a = 16 ∧ t = 2) ∨ (a = 15 ∧ t = 2) ∨ (a = 15 ∧ t = 3)) :
    (a+3)*(t+1) < (2*t+1)*(16-t) := by
  rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> norm_num

theorem all_singletons_common_neighbour (a : ℕ) (ha : 15 ≤ a) (hb : a ≤ 17) :
    0 < 2*(17-(36-2*a))-(a+3) := by
  interval_cases a <;> norm_num

/-- factor_small_order §2: disconnected critical complements are excluded
by these inequalities, for k=10 and k=11 and every c=2,...,5. -/
theorem factor_component_obstruction (k c n : ℕ)
    (hk : k = 10 ∨ k = 11) (hc : 2 ≤ c) (hc' : c ≤ 5)
    (hn : 2*k-c ≤ n) : 13*c < (c-1)*n+k := by
  rcases hk with rfl|rfl <;> interval_cases c <;> omega

/-- The arithmetic classification of the five bags in dense_complement41
§5. Establishing that the graph has these bags is a separate structural task. -/
def FiveBagPattern (a b c d e : ℕ) : Prop :=
  (a = 9 ∧ b = 9 ∧ c = 7 ∧ d = 7 ∧ e = 9) ∨
  (a = 9 ∧ b = 7 ∧ c = 7 ∧ d = 9 ∧ e = 9) ∨
  (a = 7 ∧ b = 7 ∧ c = 9 ∧ d = 9 ∧ e = 9) ∨
  (a = 7 ∧ b = 9 ∧ c = 9 ∧ d = 9 ∧ e = 7) ∨
  (a = 9 ∧ b = 9 ∧ c = 9 ∧ d = 7 ∧ e = 7) ∨
  (a = 9 ∧ b = 9 ∧ c = 8 ∧ d = 7 ∧ e = 8) ∨
  (a = 9 ∧ b = 8 ∧ c = 7 ∧ d = 8 ∧ e = 9) ∨
  (a = 8 ∧ b = 7 ∧ c = 8 ∧ d = 9 ∧ e = 9) ∨
  (a = 7 ∧ b = 8 ∧ c = 9 ∧ d = 9 ∧ e = 8) ∨
  (a = 8 ∧ b = 9 ∧ c = 9 ∧ d = 8 ∧ e = 7) ∨
  (a = 8 ∧ b = 8 ∧ c = 8 ∧ d = 8 ∧ e = 9) ∨
  (a = 8 ∧ b = 8 ∧ c = 8 ∧ d = 9 ∧ e = 8) ∨
  (a = 8 ∧ b = 8 ∧ c = 9 ∧ d = 8 ∧ e = 8) ∨
  (a = 8 ∧ b = 9 ∧ c = 8 ∧ d = 8 ∧ e = 8) ∨
  (a = 9 ∧ b = 8 ∧ c = 8 ∧ d = 8 ∧ e = 8)

set_option maxHeartbeats 2000000 in
theorem five_bag_sizes (a b c d e : ℕ)
    (hs : a+b+c+d+e = 41)
    (h0 : 16 ≤ e+b) (h1 : 16 ≤ a+c) (h2 : 16 ≤ b+d)
    (h3 : 16 ≤ c+e) (h4 : 16 ≤ d+a) : FiveBagPattern a b c d e := by
  have ha : 7 ≤ a ∧ a ≤ 9 := by omega
  have hb : 7 ≤ b ∧ b ≤ 9 := by omega
  have hc : 7 ≤ c ∧ c ≤ 9 := by omega
  have hd : 7 ≤ d ∧ d ≤ 9 := by omega
  have he : 7 ≤ e ∧ e ≤ 9 := by omega
  rcases ha with ⟨ha,ha'⟩
  rcases hb with ⟨hb,hb'⟩
  rcases hc with ⟨hc,hc'⟩
  rcases hd with ⟨hd,hd'⟩
  rcases he with ⟨he,he'⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    interval_cases d <;> interval_cases e <;> norm_num [FiveBagPattern] at *

end Se20Part.CriticalSizeChecks
