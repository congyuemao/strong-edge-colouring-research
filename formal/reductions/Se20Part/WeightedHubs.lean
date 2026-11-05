import Se20Part.WeightedExchange
import Mathlib.Combinatorics.SimpleGraph.LineGraph

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
namespace Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H R : SimpleGraph W)

def tightClasses (d : C → ℕ) (π : W → C) (x : W) : Finset C :=
  Finset.univ.filter (fun c => degreeIn H π x c = d c)

theorem tight_count_bound {d : C → ℕ} {π : W → C}
    (hπ : WeightedMinimum H d π) (x : W) (hx : degreeIn H π x (π x) = d (π x)) :
    (Fintype.card C : ℤ) + (∑ c, (d c : ℤ)) - H.degree x ≤ (tightClasses H d π x).card := by
  have hh (c : C) : (d c : ℤ)+1 - (if degreeIn H π x c = d c then 1 else 0) ≤ degreeIn H π x c := by
    have hs := weighted_minimum_slack_le H hπ x c
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hh c)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,sum_degreeIn] at hs
  have hc : (∑ c, if degreeIn H π x c = d c then (1 : ℤ) else 0) =
      (tightClasses H d π x).card := by
    simp only [tightClasses,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hc] at hs
  omega

theorem weighted_bad_hub_zero {π : W → Fin 12}
    (hπ : CliqueMinimumThree H R brooksPalette π)
    (hΔ : ∀ v, H.degree v ≤ 24) (hR : ∀ v, R.degree v ≤ 6)
    {T : Finset W} (hT : T ∈ badCliques H brooksPalette π) {x : W} (hx : x ∈ T) :
    degreeIn R π x (π x) = 0 := by
  have hsum : (∑ c : Fin 12, (brooksPalette c : ℤ)) = 20 := by
    exact_mod_cast brooksPalette_sum
  have hbudget (v : W) : (H.degree v : ℤ) < ∑ c : Fin 12, ((brooksPalette c : ℤ)+1) := by
    simp only [Finset.sum_add_distrib,hsum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one]
    have := hΔ v
    omega
  have hown := badClique_own_degree H (lovasz_degree_bound H hπ.1.1 hbudget) hT hx
  have hcount := tight_count_bound H hπ.1.1 x hown
  simp only [Fintype.card_fin,hsum] at hcount
  have hlow : (8 : ℤ) ≤ (tightClasses H brooksPalette π x).card := by
    have := hΔ x
    omega
  have hpoint (c : Fin 12) :
      (if degreeIn H π x c = brooksPalette c then degreeIn R π x (π x) else 0) ≤ degreeIn R π x c := by
    split_ifs with hc
    · exact weighted_clique_hub_monotone H R hπ hbudget hT hx c hc
    · exact degreeIn_nonneg R π x c
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  rw [sum_degreeIn] at hs
  have he : (∑ c : Fin 12, if degreeIn H π x c = brooksPalette c then degreeIn R π x (π x) else 0) =
      (tightClasses H brooksPalette π x).card * degreeIn R π x (π x) := by
    rw [← Finset.sum_filter]
    simp only [tightClasses,Finset.sum_const,nsmul_eq_mul]
  rw [he] at hs
  have hp := degreeIn_nonneg R π x (π x)
  have hd := hR x
  nlinarith

end Partition

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem lineGraph_degree_le_six (hΔ : MaxDegreeFour G) (e : G.edgeSet) :
    G.lineGraph.degree e ≤ 6 := by
  have he : G.lineGraph.neighborFinset e = hubs G e := by
    ext f
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.lineGraph_adj_iff_exists,
      hubs,Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
  exact hubs_card_le_six G hΔ e

end Se20Part
