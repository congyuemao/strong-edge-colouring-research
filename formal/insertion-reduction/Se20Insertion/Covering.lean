import Se20Insertion.GraphBasics
import Se20Insertion.Kempe

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def LocallyInjective (π : G →g H) : Prop :=
  ∀ v x y, G.Adj v x → G.Adj v y → π x = π y → x = y

def LocallySurjective (π : G →g H) : Prop :=
  ∀ v y, H.Adj (π v) y → ∃ x, G.Adj v x ∧ π x = y

theorem map_edge_eq_of_incident (π : G →g H) (hi : LocallyInjective π)
    {e f : G.edgeSet} {x : V} (he : x ∈ e.val) (hf : x ∈ f.val)
    (hm : π.mapEdgeSet e = π.mapEdgeSet f) : e = f := by
  obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨v,hv⟩ := Sym2.mem_iff_exists.mp hf
  have hxu := G.mem_edgeSet.mp (hu ▸ e.2)
  have hxv := G.mem_edgeSet.mp (hv ▸ f.2)
  have hmap := congrArg Subtype.val hm
  change Sym2.map π e.val = Sym2.map π f.val at hmap
  rw [hu,hv] at hmap
  have hp : π u = π v := by
    have h' : π u = π v ∨ π x = π v ∧ π u = π x := by simpa using hmap
    exact h'.elim id (fun h => h.2.trans h.1)
  have huv := hi x u v hxu hxv hp
  apply Subtype.ext
  rw [hu,hv,huv]

/-- Local injectivity, rather than global injectivity, preserves conflicts. -/
def L2LocalMap (π : G →g H) (hi : LocallyInjective π) : L2 G →g L2 H where
  toFun := π.mapEdgeSet
  map_rel' := by
    rintro e f ⟨hne,x,hx,y,hy,hxy⟩
    refine ⟨?_,π x,Sym2.mem_map.mpr ⟨x,hx,rfl⟩,π y,
      Sym2.mem_map.mpr ⟨y,hy,rfl⟩,hxy.elim (fun h => Or.inl (congrArg π h)) (fun h => Or.inr (π.map_adj h))⟩
    intro hm
    apply hne
    rcases hxy with rfl | hxy
    · exact map_edge_eq_of_incident π hi hx hy hm
    · obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp hx
      have hxu := G.mem_edgeSet.mp (hu ▸ e.2)
      have hym : π y ∈ (π.mapEdgeSet e).val := hm ▸ Sym2.mem_map.mpr ⟨y,hy,rfl⟩
      change π y ∈ Sym2.map π e.val at hym
      rw [hu] at hym
      have hyp : π y = π u := (Sym2.mem_iff.mp hym).resolve_left (π.map_adj hxy).ne.symm
      have hyu := hi x y u hxy hxu hyp
      have hye : y ∈ e.val := by rw [hu,hyu]; simp
      exact map_edge_eq_of_incident π hi hye hy hm

/-- Pull-back corollary at line 215, for any number of colours. -/
theorem strongColourable_pullback (π : G →g H) (hi : LocallyInjective π) {K : ℕ}
    (hc : StrongColourable H K) : StrongColourable G K := by
  obtain ⟨c⟩ := hc
  exact ⟨c.comap (L2LocalMap π hi)⟩

theorem L2LocalMap_surjective_neighbours (π : G →g H) (hi : LocallyInjective π)
    (hs : LocallySurjective π) : LocallySurjective (L2LocalMap π hi) := by
  rintro e f ⟨hne,A,hA,B,hB,hAB⟩
  obtain ⟨x,hx,hxA⟩ := Sym2.mem_map.mp hA
  obtain ⟨y,hxy,hyB⟩ : ∃ y, (x = y ∨ G.Adj x y) ∧ π y = B := by
    rcases hAB with h | h
    · exact ⟨x,Or.inl rfl,hxA.trans h⟩
    · obtain ⟨y,hxy,hy⟩ := hs x B (hxA ▸ h)
      exact ⟨y,Or.inr hxy,hy⟩
  obtain ⟨C,hC⟩ := Sym2.mem_iff_exists.mp hB
  have hBC : H.Adj B C := H.mem_edgeSet.mp (hC ▸ f.2)
  obtain ⟨z,hyz,hz⟩ := hs y C (hyB ▸ hBC)
  let g : G.edgeSet := ⟨s(y,z),hyz⟩
  have hgf : π.mapEdgeSet g = f := by
    apply Subtype.ext
    change s(π y,π z) = f.val
    rw [hyB,hz,hC]
  refine ⟨g,⟨?_,x,hx,y,by simp [g],hxy⟩,hgf⟩
  intro heg
  exact hne (heg ▸ hgf)

namespace PartialColouring
variable {X Y : Type*} {A : SimpleGraph X} {B : SimpleGraph Y} {F : Finset Y}

def pullback [Fintype X] (φ : PartialColouring B F) (π : A →g B) :
    PartialColouring A (Finset.univ.filter (fun x => π x ∈ F)) where
  colour x := φ.colour (π x)
  proper := by
    intro x y hx hy hxy
    exact φ.proper (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (π.map_adj hxy)

theorem pullback_neighbour [Fintype X] (φ : PartialColouring B F) (π : A →g B)
    {v x : X} {c : Colour} (hx : (φ.pullback π).Neighbour v c x) :
    φ.Neighbour (π v) c (π x) :=
  ⟨(Finset.mem_filter.mp hx.1).2,π.map_adj hx.2.1,hx.2.2⟩

theorem pullback_sameComponent [Fintype X] (φ : PartialColouring B F) (π : A →g B)
    {a b : Colour} {x y : X} (hc : (φ.pullback π).SameComponent a b x y) :
    φ.SameComponent a b (π x) (π y) := by
  obtain ⟨hx,hy,hr⟩ := hc
  let f : (φ.pullback π).KempeGraph a b →g φ.KempeGraph a b :=
    { toFun := fun z => ⟨π z.val, (Finset.mem_filter.mp z.2.1).2,z.2.2⟩
      map_rel' := fun h => π.map_adj h }
  exact ⟨(f ⟨x,hx⟩).2,(f ⟨y,hy⟩).2,hr.map f⟩

/-- Lemma 11.2(2) for a locally surjective conflict homomorphism. -/
theorem pullback_blocked [Fintype X] (φ : PartialColouring B F) (π : A →g B)
    (hs : LocallySurjective π) {v : X}
    (hb : ∀ c, ∃ y, φ.Neighbour (π v) c y) :
    ∀ c, ∃ x, (φ.pullback π).Neighbour v c x := by
  intro c
  obtain ⟨y,hy⟩ := hb c
  obtain ⟨x,hx,hπ⟩ := hs v y hy.2.1
  exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hπ ▸ hy.1⟩,hx,
    by change φ.colour (π x) = c; rw [hπ]; exact hy.2.2⟩

/-- Lemma 11.2(3); no surjectivity is needed for separability. -/
theorem pullback_separable [Fintype X] (φ : PartialColouring B F) (π : A →g B)
    {v : X} {a b : Colour} (hs : φ.Separable (π v) a b) :
    (φ.pullback π).Separable v a b := by
  intro x y hx hy hc
  exact hs (π x) (π y) (φ.pullback_neighbour π hx) (φ.pullback_neighbour π hy)
    (φ.pullback_sameComponent π hc)

end PartialColouring
end Se20Insertion
