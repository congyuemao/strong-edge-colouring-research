import Se20Insertion.MultiplicityIdentity
import Se20Insertion.HoleCycleRank
import Se20Insertion.Theorem1144

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace Se20Insertion.PartialColouring
variable {W : Type*} [Fintype W] {H : SimpleGraph W} {F : Finset W}

def Exposed (φ : PartialColouring H F) (R : Finset W) (f w : W) : Prop :=
  ∃ g ∈ R, φ.DoubleHoleConfig g f w

def unexposedPartners (φ : PartialColouring H F) (R S : Finset W) (f : W) : Finset W :=
  (φ.partners S f).filter (fun w => ¬ φ.Exposed R f w)

def bothNonsingleGraph (φ : PartialColouring H F) : SimpleGraph W where
  Adj x y := H.Adj x y ∧ ¬ φ.Single x (φ.colour y) y ∧ ¬ φ.Single y (φ.colour x) x
  symm := ⟨by intro x y h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- All eight quantities in the manuscript's P2 identity. Integers prevent
silent truncation; Z counts unordered edges of the actual both-nonsingle graph. -/
structure P2Terms where
  n : ℤ
  D : ℤ
  B : ℤ
  M : ℤ
  T : ℤ
  E : ℤ
  Z : ℤ
  L : ℤ

def p2Terms (φ : PartialColouring H F) (R S : Finset W) (ε : W → ℕ) : P2Terms where
  n := S.card
  D := ∑ x ∈ S, φ.deficit x
  B := ∑ x ∈ S, ((φ.partners S x).filter (φ.Exposed R x)).card
  M := ∑ x ∈ S, ε x
  T := ∑ x ∈ S, (F.filter (fun y => H.Adj x y ∧ y ∉ S)).card
  E := ∑ x ∈ S, φ.excess x
  Z := ComponentInsertion.edges φ.bothNonsingleGraph S
  L := ∑ x ∈ S, (24 - ((φ.singleTargets S x).card : ℤ) - 3 * (φ.unexposedPartners R S x).card)

/-- The slack in `p2Terms` is exactly the manuscript's sum of s+epsilon-3c0,
where s counts coloured neighbours outside S and neighbours inside S at which
the colour of x is not single. -/
theorem p2_slack_eq (φ : PartialColouring H F) (R S : Finset W) (ε : W → ℕ)
    (hSF : S ⊆ F) (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card + ε x = 24) :
    (φ.p2Terms R S ε).L = ∑ x ∈ S,
      ((((φ.colouredNeighbours x).card - (φ.singleTargets S x).card + ε x : ℕ) : ℤ) -
        3 * (φ.unexposedPartners R S x).card) := by
  apply Finset.sum_congr rfl
  intro x hx
  have hs : φ.singleTargets S x ⊆ φ.colouredNeighbours x := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨hSF (Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2.1⟩
  have hl := Finset.card_le_card hs
  have hd := hdegree x hx
  omega

/-- P2's exact identity on a degree-24 conflict graph. No saturation or
absence of double-hole configurations is assumed. -/
theorem p2_identity (φ : PartialColouring H F) (R S : Finset W) (ε : W → ℕ)
    (hSF : S ⊆ F) (hclosed : φ.SingleClosed S)
    (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card + ε x = 24) :
    let v := φ.p2Terms R S ε
    14*v.D + 3*v.B = 2*v.n + 10*v.M + 3*v.T + 7*v.E + 6*v.Z + v.L := by
  let d := fun x => (φ.colouredNeighbours x).card
  let r := fun x => (S.filter (H.Adj x)).card
  let t := fun x => (F.filter (fun y => H.Adj x y ∧ y ∉ S)).card
  let y := fun x => (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single z (φ.colour x) x)).card
  let b := fun x => (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)).card
  let ns := fun x => ((φ.colouredNeighbours x).filter (fun z => ¬ φ.Single x (φ.colour z) z)).card
  let c := fun x => (φ.partners S x).card
  let z := fun x => (S.filter (φ.bothNonsingleGraph.Adj x)).card
  have hdr (x : W) : d x = r x + t x := card_filter_partition hSF (H.Adj x)
  have hns (x : W) (hx : x ∈ S) : ns x = b x + t x := by
    have hp := card_filter_partition hSF (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)
    have hout : F.filter (fun z => (H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z) ∧ z ∉ S) =
        F.filter (fun z => H.Adj x z ∧ z ∉ S) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1,h.2.1.1,h.2.2⟩
      · exact fun h => ⟨h.1,⟨h.2.1,fun hs => h.2.2 (hclosed x hx z hs)⟩,h.2.2⟩
    have hp' : (F.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)).card = b x + t x := by
      convert hp using 1
      · congr 1; ext z; simp only [Finset.mem_filter]
      · dsimp [b,t]
        congr 1
        · congr 1; ext z; simp only [Finset.mem_filter]
        · convert (congrArg Finset.card hout).symm using 1
          congr 1; ext z; simp only [Finset.mem_filter]
    simpa only [ns,b,t,colouredNeighbours,Finset.filter_filter] using hp'
  have hby : (∑ x ∈ S, b x) = ∑ x ∈ S, y x := by
    dsimp [b,y]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x hx
    apply Finset.sum_congr rfl; intro w hw
    have ha : H.Adj w x ↔ H.Adj x w := ⟨SimpleGraph.Adj.symm,SimpleGraph.Adj.symm⟩
    simp only [ha]
  have hr (x : W) : r x + z x = c x + y x + b x := by
    simp only [r,z,c,y,b,partners,bothNonsingleGraph,Finset.card_eq_sum_ones,Finset.sum_filter]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    have ha : φ.Single x (φ.colour w) w → H.Adj x w := fun h => h.1.2.1
    by_cases hadj : H.Adj x w <;>
      by_cases hsw : φ.Single x (φ.colour w) w <;>
      by_cases hsx : φ.Single w (φ.colour x) x <;> simp_all [MutualSingle]
  have htargets (x : W) : (φ.singleTargets S x).card + y x = r x := by
    have hp := Finset.card_filter_add_card_filter_not
      (s := S.filter (H.Adj x)) (fun w => φ.Single w (φ.colour x) x)
    simpa only [singleTargets,y,r,Finset.filter_filter] using hp
  have hparts (x : W) : ((φ.partners S x).filter (φ.Exposed R x)).card +
      (φ.unexposedPartners R S x).card = c x :=
    Finset.card_filter_add_card_filter_not (φ.Exposed R x)
  have hdeg := Finset.sum_congr rfl hdegree
  have hbudget := Finset.sum_congr rfl (fun x hx => φ.nonsingle_exact (hSF hx))
  have hnsum := Finset.sum_congr rfl hns
  have hdrsum := Finset.sum_congr rfl (fun x (_ : x ∈ S) => hdr x)
  have hrsum := Finset.sum_congr rfl (fun x (_ : x ∈ S) => hr x)
  have htsum := Finset.sum_congr rfl (fun x (_ : x ∈ S) => htargets x)
  have hpsum := Finset.sum_congr rfl (fun x (_ : x ∈ S) => hparts x)
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,← Finset.mul_sum] at hdeg hbudget hnsum hdrsum hrsum htsum hpsum
  rw [hby] at hnsum hrsum
  have hz : (∑ x ∈ S, z x) = 2 * ComponentInsertion.edges φ.bothNonsingleGraph S :=
    (ComponentInsertion.twice_edges φ.bothNonsingleGraph S).symm
  rw [hz] at hrsum
  have hdeg' : (∑ x ∈ S, (d x : ℤ)) + ∑ x ∈ S, (ε x : ℤ) = 24 * S.card := by
    have hh : (∑ x ∈ S, d x) + ∑ x ∈ S, ε x = 24 * S.card := by simpa [d,Nat.mul_comm] using hdeg
    exact_mod_cast hh
  have hbud' : (∑ x ∈ S, (ns x : ℤ)) + 38 * S.card + ∑ x ∈ S, (φ.excess x : ℤ) =
      2 * (∑ x ∈ S, (d x : ℤ)) + 2 * ∑ x ∈ S, (φ.deficit x : ℤ) := by
    have hh : (∑ x ∈ S, ns x) + 38 * S.card + ∑ x ∈ S, φ.excess x =
        2 * (∑ x ∈ S, d x) + 2 * ∑ x ∈ S, φ.deficit x := by simpa [ns,d,Nat.mul_comm] using hbudget
    exact_mod_cast hh
  have hns' : (∑ x ∈ S, (ns x : ℤ)) = (∑ x ∈ S, (y x : ℤ)) + ∑ x ∈ S, (t x : ℤ) := by exact_mod_cast hnsum
  have hdr' : (∑ x ∈ S, (d x : ℤ)) = (∑ x ∈ S, (r x : ℤ)) + ∑ x ∈ S, (t x : ℤ) := by exact_mod_cast hdrsum
  have hr' : (∑ x ∈ S, (r x : ℤ)) + 2 * (ComponentInsertion.edges φ.bothNonsingleGraph S : ℤ) =
      (∑ x ∈ S, (c x : ℤ)) + 2 * ∑ x ∈ S, (y x : ℤ) := by
    have hh : (∑ x ∈ S, r x) + 2 * ComponentInsertion.edges φ.bothNonsingleGraph S =
        (∑ x ∈ S, c x) + 2 * ∑ x ∈ S, y x := by omega
    exact_mod_cast hh
  have ht' : (∑ x ∈ S, ((φ.singleTargets S x).card : ℤ)) + ∑ x ∈ S, (y x : ℤ) =
      ∑ x ∈ S, (r x : ℤ) := by exact_mod_cast htsum
  have hp' : (∑ x ∈ S, (((φ.partners S x).filter (φ.Exposed R x)).card : ℤ)) +
      ∑ x ∈ S, ((φ.unexposedPartners R S x).card : ℤ) = ∑ x ∈ S, (c x : ℤ) := by exact_mod_cast hpsum
  dsimp only [p2Terms]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,Nat.cast_sum]
  change 14 * (∑ x ∈ S, (φ.deficit x : ℤ)) + 3 * (∑ x ∈ S, (((φ.partners S x).filter (φ.Exposed R x)).card : ℤ)) = _
  dsimp only [t] at hdr' hns'
  omega

end Se20Insertion.PartialColouring
