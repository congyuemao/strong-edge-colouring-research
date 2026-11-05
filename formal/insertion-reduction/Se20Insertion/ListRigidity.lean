import Se20Insertion.DegreeThreeRigidity
import Se20Insertion.ListExtensions

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

def OneSwapListRepair (φ : PartialColouring H F) (U : Finset W) : Prop :=
  ∃ ψ : PartialColouring H F, (ψ = φ ∨ φ.OneKempeSwap ψ) ∧
    ∃ θ : PartialColouring H (F ∪ U), ∀ x ∈ F, θ.colour x = ψ.colour x

theorem available_complement (φ : PartialColouring H F) (v : W) :
    (φ.colouredNeighbours v).image φ.colour = Finset.univ \ φ.available v := by
  ext c; simp [colouredNeighbours,available,Free,Neighbour,and_assoc]

theorem tight_list_neighbours (φ : PartialColouring H F) (v : W)
    (hn : (φ.colouredNeighbours v).card + (φ.available v).card ≤ 20) :
    (φ.colouredNeighbours v).card + (φ.available v).card = 20 ∧
    Set.InjOn φ.colour (φ.colouredNeighbours v) ∧
    ∀ c ∉ φ.available v, ∃! x, φ.Neighbour v c x := by
  have hi := Finset.card_image_le (s := φ.colouredNeighbours v) (f := φ.colour)
  have hp := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour) (φ.available v)
  rw [← φ.available_complement,Finset.univ_inter] at hp
  have hc : (Finset.univ : Finset Colour).card = 20 := rfl
  rw [hc] at hp
  have heq : ((φ.colouredNeighbours v).image φ.colour).card = (φ.colouredNeighbours v).card := by omega
  have hinj := Finset.card_image_iff.mp heq
  refine ⟨by omega, hinj, ?_⟩
  intro c hc
  have hm : c ∈ (φ.colouredNeighbours v).image φ.colour := by rw [φ.available_complement]; simp [hc]
  obtain ⟨x,hx,hxc⟩ := Finset.mem_image.mp hm
  refine ⟨x, ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2,hxc⟩, ?_⟩
  intro y hy
  exact hinj (Finset.mem_filter.mpr ⟨hy.1,hy.2.1⟩) hx (hy.2.2.trans hxc.symm)

theorem swap_unique_list (φ : PartialColouring H F) {v m : W} {a b : Colour}
    (ha : a ∈ φ.available v) (hs : φ.Single v b m) {S : Set W}
    (hS : φ.KempeClosed a b S) :
    (φ.swap a b S hS).available v =
      if m ∈ S then insert b ((φ.available v).erase a) else φ.available v := by
  have haf : φ.Free v a := (Finset.mem_filter.mp ha).2
  have hb : b ∉ φ.available v := fun h => (Finset.mem_filter.mp h).2 ⟨m,hs.1⟩
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hf : ∀ x, φ.Neighbour v a x → False := fun x hx => haf ⟨x,hx⟩
  have all : (∀ x, φ.Neighbour v b x → x ∈ S) ↔ m ∈ S :=
    ⟨fun h => h m hs.1, fun h x hx => hs.2 x hx ▸ h⟩
  have none : (∀ x, φ.Neighbour v b x → x ∉ S) ↔ m ∉ S :=
    ⟨fun h => h m hs.1, fun h x hx => hs.2 x hx ▸ h⟩
  ext c
  by_cases hca : c = a
  · subst c
    simp only [available,Finset.mem_filter,Finset.mem_univ,true_and,φ.swap_free_left_iff hS]
    rw [and_iff_right (fun x hx => (hf x hx).elim),none]
    by_cases hm : m ∈ S <;> simp [hm,hab,haf,available]
  by_cases hcb : c = b
  · subst c
    simp only [available,Finset.mem_filter,Finset.mem_univ,true_and,φ.swap_free_right_iff hS]
    rw [and_iff_left (fun x hx => (hf x hx).elim),all]
    by_cases hm : m ∈ S <;> simp_all [available]
  have hsame : c ∈ (φ.swap a b S hS).available v ↔ c ∈ φ.available v := by
    simp only [available,Finset.mem_filter,Finset.mem_univ,true_and,Free,Neighbour,swap,
      φ.swapColour_eq_iff hca hcb]
  by_cases hm : m ∈ S <;> simp [hm,hca,hcb,hsame]

/-- Common-list rigidity and connectivity, for both three and six outgoing edges. -/
theorem one_swap_list_rigidity (φ : PartialColouring H F) (U : Finset W)
    (hdis : Disjoint F U) (hne : U.Nonempty)
    (hL : ∀ v ∈ U, U.card - 1 ≤ (φ.available v).card)
    (hN : ∀ v ∈ U, (φ.colouredNeighbours v).card + (U.card - 1) ≤ 20)
    (hno : ¬ φ.OneSwapListRepair U) :
    ∃ L : Finset Colour, L.card = U.card - 1 ∧
      (∀ v ∈ U, φ.available v = L) ∧
      (∀ v ∈ U, (φ.colouredNeighbours v).card + L.card = 20 ∧
        ∀ b ∉ L, ∃! m, φ.Neighbour v b m) ∧
      ∀ a ∈ L, ∀ b ∉ L, ∀ v ∈ U, ∀ w ∈ U, ∀ m n,
        φ.Neighbour v b m → φ.Neighbour w b n → φ.SameComponent a b m n := by
  haveI : Nonempty U := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have nochoice (ψ : PartialColouring H F) (hop : ψ = φ ∨ φ.OneKempeSwap ψ) :
      ¬ ∃ c : U → Colour, Function.Injective c ∧ ∀ v, c v ∈ ψ.available v.val := by
    rintro ⟨c,hinj,hc⟩
    have hf : ∀ v : U, ψ.Free v.val (c v) := fun v => (Finset.mem_filter.mp (hc v)).2
    exact hno ⟨ψ,hop,ψ.fillLists U c hinj hf,ψ.fillLists_agrees U c hinj hf hdis⟩
  obtain ⟨L,hcard,hlist⟩ := almost_full_lists (fun v : U => φ.available v.val)
    (by simpa only [Fintype.card_coe] using fun v : U => hL v.val v.property)
    (nochoice φ (Or.inl rfl))
  rw [Fintype.card_coe] at hcard
  have lists (v : W) (hv : v ∈ U) : φ.available v = L := hlist ⟨v,hv⟩
  have tight (v : W) (hv : v ∈ U) := φ.tight_list_neighbours v
    (by rw [lists v hv,hcard]; exact hN v hv)
  have unique (v : W) (hv : v ∈ U) (b : Colour) (hb : b ∉ L) : ∃! m, φ.Neighbour v b m :=
    (tight v hv).2.2 b (by rw [lists v hv]; exact hb)
  refine ⟨L,hcard,lists,?_,?_⟩
  · intro v hv; exact ⟨by rw [← lists v hv]; exact (tight v hv).1, unique v hv⟩
  · intro a ha b hb v hv w hw m n hm hn
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    let S := {x | φ.SameComponent a b m x}
    let ψ := φ.swap a b S (φ.component_closed a b m)
    have hmS : m ∈ S := φ.sameComponent_refl ⟨hm.1,Or.inr hm.2.2⟩
    have sing (x : W) (hx : x ∈ U) (y : W) (hy : φ.Neighbour x b y) : φ.Single x b y := by
      obtain ⟨z,hz,hu⟩ := unique x hx b hb
      exact ⟨hy,fun t ht => (hu t ht).trans (hu y hy).symm⟩
    have update (x : W) (hx : x ∈ U) (y : W) (hy : φ.Neighbour x b y) :
        ψ.available x = if y ∈ S then insert b (L.erase a) else L := by
      have hh := φ.swap_unique_list (by rw [lists x hx]; exact ha) (sing x hx y hy)
        (φ.component_closed a b m)
      simpa only [lists x hx] using hh
    have hlen : ∀ x : U, Fintype.card U - 1 ≤ (ψ.available x.val).card := by
      intro x
      obtain ⟨y,hy,_⟩ := unique x.val x.property b hb
      rw [update x.val x.property y hy]
      have he := Finset.card_erase_add_one ha
      have hnins : b ∉ L.erase a := fun h => hb (Finset.mem_of_mem_erase h)
      by_cases hyS : y ∈ S <;> simp only [hyS,ite_true,ite_false,Finset.card_insert_of_notMem hnins]
      all_goals rw [Fintype.card_coe]; omega
    obtain ⟨L',_,hlist'⟩ := almost_full_lists (fun x : U => ψ.available x.val) hlen
      (nochoice ψ (Or.inr ⟨a,b,hab,m,⟨hm.1,Or.inr hm.2.2⟩,fun _ => rfl⟩))
    have same : ψ.available v = ψ.available w := (hlist' ⟨v,hv⟩).trans (hlist' ⟨w,hw⟩).symm
    rw [update v hv m hm,update w hw n hn,if_pos hmS] at same
    by_contra hnS
    change n ∉ S at hnS
    rw [if_neg hnS] at same
    exact hb (same ▸ Finset.mem_insert_self b (L.erase a))

end Se20Insertion.PartialColouring
