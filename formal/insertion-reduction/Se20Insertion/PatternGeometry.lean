import Se20Insertion.LoopChains
import Se20Insertion.P2Geometry

noncomputable section
open scoped Classical
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.TreePattern
open GirthGeometry
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem opposite_near_far_not_close (hg : 7 ≤ G.egirth) {u v x y z : V}
    (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y) (hyz : G.Adj y z)
    (hxv : x ≠ v) (hyu : y ≠ u) (hzv : z ≠ v) :
    ¬ Close (G := G) u x y z := by
  intro hc
  simp only [Close] at hc
  rcases hc with h | h | h | h | h | h | h | h <;>
    grind (instances := 2000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm,
      → no_triangle, → square_backtrack, → pentagon_backtrack]

theorem same_side_far_close (hg : 7 ≤ G.egirth) {u x y z t : V}
    (hux : G.Adj u x) (huy : G.Adj u y) (hxz : G.Adj x z) (hyt : G.Adj y t)
    (hzu : z ≠ u) (htu : t ≠ u) (hc : Close (G := G) x z y t) : x = y := by
  simp only [Close] at hc
  rcases hc with h | h | h | h | h | h | h | h <;>
    grind (instances := 2000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm,
      → no_triangle, → square_backtrack, → pentagon_backtrack]

theorem opposite_far_not_close (hg : 7 ≤ G.egirth) {u v x y z t : V}
    (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y)
    (hxz : G.Adj x z) (hyt : G.Adj y t)
    (hxv : x ≠ v) (hyu : y ≠ u) (hzu : z ≠ u) (htv : t ≠ v) :
    ¬ Close (G := G) x z y t := by
  intro hc
  simp only [Close] at hc
  rcases hc with h | h | h | h | h | h | h | h <;>
    grind (instances := 3000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm,
      → no_triangle, → square_backtrack, → pentagon_backtrack, → hexagon_backtrack]

/-- The labels are chosen from the actual three neighbours other than the parent. -/
def children (hreg : FourRegular G) (a b : V) (hab : G.Adj a b) :
    Fin 3 ≃ ↥((G.neighborFinset a).erase b) :=
  (Finset.equivFinOfCardEq (by
    have hc := Finset.card_erase_add_one ((G.mem_neighborFinset a b).mpr hab)
    rw [SimpleGraph.card_neighborFinset_eq_degree, hreg] at hc
    omega)).symm

theorem exists_geometric_label (hreg : FourRegular G) (hg : 7 ≤ G.egirth)
    (e : G.edgeSet) :
    ∃ ι : Position ≃ ↥(conflicts G e),
      ∀ x y, (L2 G).Adj (ι x).val (ι y).val → graph.Adj x y := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  let r : Bool → V := fun s => if s then v else u
  have hr (s : Bool) : G.Adj (r s) (r (!s)) := by cases s <;> simp [r,huv,huv.symm]
  let X (i : Branch) := children hreg (r i.1) (r (!i.1)) (hr i.1) i.2
  have hx (i : Branch) : G.Adj (r i.1) (X i).val :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp (X i).prop).2
  have hxn (i : Branch) : (X i).val ≠ r (!i.1) := (Finset.mem_erase.mp (X i).prop).1
  let Z (i : Branch) (j : Fin 3) := children hreg (X i).val (r i.1) (hx i).symm j
  have hz (i : Branch) (j : Fin 3) : G.Adj (X i).val (Z i j).val :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp (Z i j).prop).2
  have hzn (i : Branch) (j : Fin 3) : (Z i j).val ≠ r i.1 := (Finset.mem_erase.mp (Z i j).prop).1
  let f : Position → G.edgeSet := fun p => match p with
    | .inl i => edge G (hx i)
    | .inr (i,j) => edge G (hz i j)
  have hXrim (i : Branch) : (X i).val ∈ rim G u v := by
    have hm := (X i).prop
    rcases i with ⟨s,i⟩
    cases s
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ hm
  have hf (p : Position) : f p ∈ conflicts G e := by
    rw [conflicts_eq_rim G e he]
    rcases p with i | ⟨i,j⟩
    · exact Finset.mem_biUnion.mpr ⟨(X i).val,hXrim i,by simp [f,edge]⟩
    · exact Finset.mem_biUnion.mpr ⟨(X i).val,hXrim i,by simp [f,edge]⟩
  let f' : Position → ↥(conflicts G e) := fun p => ⟨f p,hf p⟩
  have hsur : Function.Surjective f' := by
    intro w
    have hw := (Finset.ext_iff.mp (conflicts_eq_rim G e he) w.val).mp w.prop
    obtain ⟨x,hxr,hxw⟩ := Finset.mem_biUnion.mp hw
    have hxw := (mem_incident G x w.val).mp hxw
    obtain ⟨z,hwz⟩ := Sym2.mem_iff_exists.mp hxw
    have hxz : G.Adj x z := G.mem_edgeSet.mp (hwz ▸ w.val.prop)
    have hxi : ∃ i : Branch, (X i).val = x := by
      rcases Finset.mem_union.mp hxr with hx | hx
      · obtain ⟨i,hi⟩ := (children hreg u v huv).surjective ⟨x,hx⟩
        exact ⟨(false,i),congrArg Subtype.val hi⟩
      · obtain ⟨i,hi⟩ := (children hreg v u huv.symm).surjective ⟨x,hx⟩
        exact ⟨(true,i),congrArg Subtype.val hi⟩
    obtain ⟨i,hi⟩ := hxi
    by_cases hzr : z = r i.1
    · refine ⟨.inl i,Subtype.ext (Subtype.ext ?_)⟩
      change s(r i.1,(X i).val) = w.val.val
      rw [hwz,hi,hzr,Sym2.eq_swap]
    · have hzmem : z ∈ (G.neighborFinset (X i).val).erase (r i.1) := by simp [hzr,hi,hxz]
      obtain ⟨j,hj⟩ := (children hreg (X i).val (r i.1) (hx i).symm).surjective ⟨z,hzmem⟩
      refine ⟨.inr (i,j),Subtype.ext (Subtype.ext ?_)⟩
      change s((X i).val,(Z i j).val) = w.val.val
      rw [hwz,show (Z i j).val = z from congrArg Subtype.val hj,hi]
  have hcard : Fintype.card Position = Fintype.card ↥(conflicts G e) := by
    rw [positions_card,Fintype.card_coe,regular_girth_conflicts_card G hreg hg]
  let ι := Equiv.ofBijective f' ((Fintype.bijective_iff_surjective_and_card f').mpr ⟨hsur,hcard⟩)
  refine ⟨ι,?_⟩
  intro a b hab
  have hne : a ≠ b := fun h => hab.ne (congrArg (fun p => (ι p).val) h)
  change (L2 G).Adj (f a) (f b) at hab
  refine ⟨hne,?_⟩
  rcases a with i | ⟨i,j⟩ <;> rcases b with k | ⟨k,l⟩
  · trivial
  · have hc := close_of_conflict (G := G) (show (f (.inl i)).val = _ from rfl)
      (show (f (.inr (k,l))).val = _ from rfl) (Or.inr hab)
    by_contra hn
    have hs : k.1 = !i.1 := by cases hi : i.1 <;> cases hk : k.1 <;> simp_all
    exact opposite_near_far_not_close hg (hr i.1) (hx i) (hs ▸ hx k)
      (hz k l) (hxn i) (by simpa [hs] using hxn k) (by simpa [hs] using hzn k l) hc
  · have hc := close_of_conflict (G := G) (show (f (.inl k)).val = _ from rfl)
      (show (f (.inr (i,j))).val = _ from rfl) (Or.inr hab.symm)
    by_contra hn
    have hs : i.1 = !k.1 := by cases hi : i.1 <;> cases hk : k.1 <;> simp_all
    exact opposite_near_far_not_close hg (hr k.1) (hx k) (hs ▸ hx i)
      (hz i j) (hxn k) (by simpa [hs] using hxn i) (by simpa [hs] using hzn i j) hc
  · have hc := close_of_conflict (G := G) (show (f (.inr (i,j))).val = _ from rfl)
      (show (f (.inr (k,l))).val = _ from rfl) (Or.inr hab)
    have hs : i.1 = k.1 := by
      by_contra hn
      have hk : k.1 = !i.1 := by cases hi : i.1 <;> cases hk : k.1 <;> simp_all
      exact opposite_far_not_close hg (hr i.1) (hx i) (hk ▸ hx k)
        (hz i j) (hz k l) (hxn i) (by simpa [hk] using hxn k)
        (hzn i j) (by simpa [hk] using hzn k l) hc
    have heq : (X i).val = (X k).val := same_side_far_close hg (hx i)
      (hs.symm ▸ hx k) (hz i j) (hz k l) (hzn i j) (by simpa [hs] using hzn k l) hc
    rcases i with ⟨s,i⟩; rcases k with ⟨t,k⟩
    dsimp at hs; subst t
    have hik : i = k := (children hreg (r s) (r (!s)) (hr s)).injective (Subtype.ext heq)
    exact Prod.ext rfl hik

end Se20Insertion.TreePattern
