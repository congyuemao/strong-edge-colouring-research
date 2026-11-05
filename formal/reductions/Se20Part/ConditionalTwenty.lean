import Se20Part.WeightedHubs
import Se20Part.MatchingTriangle

noncomputable section
open scoped Classical
namespace Se20Part
open Partition
set_option maxHeartbeats 2000000

theorem degree_class_le {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W) (π : W → C)
    (c : C) (x : {v // π v = c}) :
    ((H.induce {v | π v = c}).degree x : ℤ) ≤ degreeIn H π x.val c := by
  let A := Finset.univ.filter (fun y => H.Adj x.val y ∧ π y = c)
  let f : (H.induce {v | π v = c}).neighborSet x → A := fun y =>
    ⟨y.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y.prop,y.val.prop⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : A => y.val) hab
  have hc := Fintype.card_le_of_injective f hf
  rw [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe] at hc
  rw [degreeIn_eq_card]
  exact_mod_cast hc

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- The precise obstruction in a one-colour class: distinct disjoint edges
at distance two in the original graph. -/
def NoRemoteMarks (π : G.edgeSet → Fin 12) : Prop :=
  ∀ e f, π e = π f → 4 ≤ (π e).val → (L2 G).Adj e f →
    ∃ v ∈ e.val, v ∈ f.val

theorem weighted_bad_clique_is_matching (hΔ : MaxDegreeFour G)
    {π : G.edgeSet → Fin 12}
    (hπ : CliqueMinimumThree (L2 G) G.lineGraph brooksPalette π)
    {T : Finset G.edgeSet} (hT : T ∈ badCliques (L2 G) brooksPalette π) :
    ∀ e ∈ T, ∀ f ∈ T, e ≠ f → ∀ v ∈ e.val, v ∉ f.val := by
  letI : DecidableEq G.edgeSet := fun a b => Classical.propDecidable (a=b)
  have hd (e : G.edgeSet) : (L2 G).degree e ≤ 24 := by
    have heq : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
    rw [← SimpleGraph.card_neighborFinset_eq_degree,heq]
    exact card_conflicts_le_twentyFour G hΔ e
  obtain ⟨c,_,hc,_⟩ := (mem_badCliques _ _ _ _).mp hT
  intro e he f hf hef v hve hvf
  have hz := weighted_bad_hub_zero (L2 G) G.lineGraph hπ hd (lineGraph_degree_le_six G hΔ) hT he
  rw [degreeIn_eq_card] at hz
  have hz0 := Int.ofNat_eq_zero.mp hz
  simp only [Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem,
    Finset.mem_filter,Finset.mem_univ,true_and] at hz0
  exact hz0 f ⟨SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef,v,hve,hvf⟩,
    (hc f hf).trans (hc e he).symm⟩

/-- Theorem 4.11, with Brooks as the sole cited theorem argument. The full
lexicographic minimum and the absence of remote marks are explicit. -/
theorem conditional_twenty (hBrooks : Brooks) (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 12}
    (hπ : CliqueMinimumThree (L2 G) G.lineGraph brooksPalette π)
    (hremote : NoRemoteMarks G π) : StrongColourable G 20 := by
  have hd (e : G.edgeSet) : (L2 G).degree e ≤ 24 := by
    have heq : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
    rw [← SimpleGraph.card_neighborFinset_eq_degree,heq]
    exact card_conflicts_le_twentyFour G hΔ e
  have hsum : (∑ c : Fin 12, (brooksPalette c : ℤ)) = 20 := by exact_mod_cast brooksPalette_sum
  have hbudget (e : G.edgeSet) : ((L2 G).degree e : ℤ) < ∑ c : Fin 12, ((brooksPalette c : ℤ)+1) := by
    simp only [Finset.sum_add_distrib,hsum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one]
    have := hd e
    omega
  have hown := lovasz_degree_bound (L2 G) hπ.1.1 hbudget
  apply brooks_partition_twenty hBrooks (L2 G) π
  · intro c x
    have hh := (degree_class_le (L2 G) π c x).trans (by simpa only [x.prop] using hown x.val)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh ⊢
    exact_mod_cast hh
  · intro c hc S hS
    let T := S.image (fun e => e.val)
    have ht : T.card = 4 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hS.card_eq
    have hcol : ∀ e ∈ T, π e = c := by
      intro e he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact f.prop
    have hcl : (L2 G).IsClique (T : Set G.edgeSet) := by
      intro e he f hf hef
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
      exact hS.isClique ha hb (fun h => hef (congrArg Subtype.val h))
    have hbad : T ∈ badCliques (L2 G) brooksPalette π :=
      (mem_badCliques _ _ _ _).mpr ⟨c,by simpa [brooksPalette,hc] using ht,hcol,hcl⟩
    obtain ⟨U,hUT,hu⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ T.card)
    exact no_matching_clique_three G hg U hu (fun _ he _ hf => hcl (hUT he) (hUT hf))
      (fun e he f hf => weighted_bad_clique_is_matching G hΔ hπ hbad e (hUT he) f (hUT hf))
  · intro c hc e f hef
    have hne := hef.ne
    let T : Finset G.edgeSet := {e.val,f.val}
    have hbad : T ∈ badCliques (L2 G) brooksPalette π := by
      apply (mem_badCliques _ _ _ _).mpr
      refine ⟨c,?_,?_,?_⟩
      · simp [T,hne,brooksPalette,show ¬ c.val < 4 by omega]
      · intro a ha
        simp only [T,Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        · exact e.prop
        · exact f.prop
      · intro a ha b hb hab
        change a ∈ T at ha
        change b ∈ T at hb
        simp only [T,Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
        · exact False.elim (hab rfl)
        · exact hef
        · exact hef.symm
        · exact False.elim (hab rfl)
    obtain ⟨v,hve,hvf⟩ := hremote e.val f.val (e.prop.trans f.prop.symm) (by simpa [e.prop] using hc) hef
    exact weighted_bad_clique_is_matching G hΔ hπ hbad e.val (by simp [T])
      f.val (by simp [T]) hne v hve hvf

end Se20Part
