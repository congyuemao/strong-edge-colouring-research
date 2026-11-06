import Se20Part.FiniteNonseparating
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part.DegreeList

variable {A W : Type*} [Fintype A] [Fintype W] [Nonempty A]
  {K : SimpleGraph A} {H : SimpleGraph W}

/-- A copy of a finite regular graph in a connected graph of the same
degree is an isomorphism. The neighbour images have equal cardinality,
so the image is closed under adjacency and hence is the entire graph. -/
theorem regular_copy_iso (f : SimpleGraph.Copy K H) (hc : H.Connected) (d : ℕ)
    (hK : ∀ x, K.degree x = d) (hH : ∀ x, H.degree x = d) : Nonempty (K ≃g H) := by
  have hn (x : A) : (K.neighborFinset x).image f = H.neighborFinset (f x) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      exact (H.mem_neighborFinset _ _).mpr (f.toHom.map_adj ((K.mem_neighborFinset _ _).mp hz))
    · rw [Finset.card_image_of_injective _ (show Function.Injective (fun a => f a) from f.injective),
        SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree,hK,hH]
  have next {x : A} {y : W} (hxy : H.Adj (f x) y) : ∃ z, K.Adj x z ∧ f z = y := by
    have hm : y ∈ (K.neighborFinset x).image f := by rw [hn]; simpa using hxy
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hm
    exact ⟨z,(K.mem_neighborFinset _ _).mp hz,hzy⟩
  have hsur : Function.Surjective f := by
    let r : A := Classical.choice inferInstance
    have go : ∀ {x y : W}, H.Walk x y → (∃ a, f a = x) → ∃ a, f a = y := by
      intro x y p
      induction p with
      | nil => exact id
      | @cons x y z hxy p ih =>
        rintro ⟨a,rfl⟩
        obtain ⟨b,_,hb⟩ := next hxy
        exact ih ⟨b,hb⟩
    intro y
    obtain ⟨p⟩ := hc (f r) y
    exact go p ⟨r,rfl⟩
  refine ⟨{ toEquiv := Equiv.ofBijective f ⟨f.injective,hsur⟩, map_rel_iff' := ?_ }⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨z,hxz,hzy⟩ := next hxy
    exact f.injective hzy ▸ hxz
  · exact f.toHom.map_adj

/-- An actual odd cycle, including its graph isomorphism. -/
def IsOddCycleGraph {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ n : ℕ, Odd (n+3) ∧ Nonempty (H ≃g SimpleGraph.cycleGraph (n+3))

set_option maxHeartbeats 800000 in
theorem regular_two_iso_cycle {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (hd : ∀ x, H.degree x = 2) :
    ∃ n : ℕ, Nonempty (H ≃g SimpleGraph.cycleGraph (n+3)) := by
  classical
  obtain ⟨r⟩ := hc.nonempty
  have hp : 0 < H.degree r := by rw [hd]; decide
  obtain ⟨s,hrs⟩ := H.degree_pos_iff_nonempty.mp hp
  have : Nontrivial W := ⟨⟨r,s,hrs.ne⟩⟩
  have hn : ¬ H.IsAcyclic := by
    intro ha
    have ht : H.IsTree := { connected := hc, isAcyclic := ha }
    obtain ⟨x,hx⟩ := ht.exists_vert_degree_one_of_nontrivial
    rw [hd] at hx
    contradiction
  obtain ⟨v,p,hp⟩ : ∃ (v : W) (p : H.Walk v v), p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hn
  have he : p.length = (p.length-3)+3 := by have := hp.three_le_length; omega
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff
    (show 2 < (p.length-3)+3 by omega)).mpr ⟨v,p,hp,he⟩
  obtain ⟨i⟩ := regular_copy_iso f hc 2 (fun x => by
    convert (SimpleGraph.cycleGraph_degree_three_le (v := x)) using 1
    exact congrArg (@SimpleGraph.degree _ _ x) (Subsingleton.elim _ _)) hd
  exact ⟨p.length-3,⟨i.symm⟩⟩

theorem regular_two_odd_of_not_colourable {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (hd : ∀ x, H.degree x = 2) (hn : ¬ H.Colorable 2) : IsOddCycleGraph H := by
  obtain ⟨n,⟨i⟩⟩ := regular_two_iso_cycle H hc hd
  refine ⟨n,?_,⟨i⟩⟩
  rcases Nat.even_or_odd (n+3) with he | ho
  · obtain ⟨c⟩ := SimpleGraph.IsBipartite.cycleGraph_of_even he
    exact (hn ⟨c.comap i.toHom⟩).elim
  · exact ho

/-- The complete no-cut bad-list classification. -/
theorem bad_noncut_complete_or_odd_cycle {W C : Type*} [Fintype W] [DecidableEq W] [Nonempty C]
    (H : SimpleGraph W) (L : W → Finset C) (hc : H.Connected)
    (hdelete : ∀ v, (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ) :
    (∀ x y, x ≠ y → H.Adj x y) ∨ IsOddCycleGraph H := by
  by_cases hcomplete : ∀ x y, x ≠ y → H.Adj x y
  · exact Or.inl hcomplete
  have hn : ∃ x y, x ≠ y ∧ ¬ H.Adj x y := by
    simpa only [not_forall,not_imp,exists_prop] using hcomplete
  obtain ⟨u,v,r,huv,hnuv,hru,hrv⟩ := exists_induced_three_path H hc hn
  have huniform := bad_noncut_uniform H L hc hdelete hd hbad r
  have htwo : 2 ≤ H.degree r := by
    have hs : ({u,v} : Finset W) ⊆ H.neighborFinset r := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hru,hrv]
    have hb := Finset.card_le_card hs
    simpa [Finset.card_pair huv] using hb
  by_cases heq : H.degree r = 2
  · right
    have hreg : ∀ x, H.degree x = 2 := fun x =>
      (huniform x).2.trans ((huniform r).2.symm.trans heq)
    apply regular_two_odd_of_not_colourable H hc hreg
    simpa [heq] using bad_noncut_not_degree_colourable H L hc hdelete hd hbad r
  · have hmin : ∀ x, 3 ≤ H.degree x := by
      intro x
      have hx := (huniform x).2
      have hr := (huniform r).2
      omega
    obtain ⟨x,y,z,hxy,hnxy,hzx,hzy,hrem⟩ :=
      FiniteConnectivity.exists_nonseparating_pair H hc hdelete hmin hn
    have hpos : 0 < (L x).card := (lt_of_lt_of_le (by decide : 0 < 3) (hmin x)).trans_le (hd x)
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
    have hleq : L y = L x := (huniform y).1.trans (huniform x).1.symm
    exact (hbad (colourable_of_nonseparating_pair H L hxy hnxy hzx hzy hrem hd ha (hleq.symm ▸ ha))).elim

end Se20Part.DegreeList
