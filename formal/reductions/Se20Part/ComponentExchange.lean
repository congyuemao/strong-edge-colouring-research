import Se20Part.Residual

noncomputable section
open scoped Classical
namespace Se20Part
variable {W : Type*} [Fintype W] (H J : SimpleGraph W)

abbrev BadComponent (H : SimpleGraph W) :=
  {K : H.ConnectedComponent // ¬ K.toSimpleGraph.Colorable 2}

theorem component_image_mem (K : J.ConnectedComponent)
    (hedge : ∀ a ∈ K.supp, ∀ b ∈ K.supp, J.Adj a b → H.Adj a b)
    {y : W} (hy : y ∈ K.supp) :
    y ∈ (H.connectedComponentMk K.out).supp := by
  let f : K.toSimpleGraph →g H := {
    toFun := Subtype.val
    map_rel' := fun {a b} h => hedge a a.prop b b.prop h }
  apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
  apply SimpleGraph.ConnectedComponent.sound
  exact ((K.connected_toSimpleGraph ⟨y,hy⟩ ⟨K.out,K.out_eq⟩).some.map f).reachable

/-- If the graphs differ only at x, a new bad component avoiding x lies in
an old bad component avoiding x. Deleting x from an old degree-two component
is bipartite; this is the essential parity input. -/
theorem bad_component_transfer (hΔ : ∀ v, H.degree v ≤ 2) (x : W)
    (heq : ∀ a b, a ≠ x → b ≠ x → (H.Adj a b ↔ J.Adj a b))
    (K : BadComponent J) (hx : x ∉ K.val.supp) :
    ¬ (H.connectedComponentMk K.val.out).toSimpleGraph.Colorable 2 ∧
      x ∉ (H.connectedComponentMk K.val.out).supp := by
  let C := H.connectedComponentMk K.val.out
  have hav {y : W} (hy : y ∈ K.val.supp) : y ≠ x := fun h => hx (h ▸ hy)
  have hmem {y : W} (hy : y ∈ K.val.supp) : y ∈ C.supp :=
    component_image_mem H J K.val
      (fun a ha b hb h => (heq a b (hav ha) (hav hb)).mpr h) hy
  let f : K.val.toSimpleGraph →g C.toSimpleGraph := {
    toFun y := ⟨y.val,hmem y.prop⟩
    map_rel' := fun {a b} h => (heq a b (hav a.prop) (hav b.prop)).mpr h }
  constructor
  · intro hc
    exact K.prop ⟨hc.some.comap f⟩
  · intro hxC
    obtain ⟨P⟩ := component_pathCycleOrder H hΔ C
    let z : C.supp := ⟨x,hxC⟩
    let f' : K.val.toSimpleGraph →g (C.toSimpleGraph.induce {y | y ≠ z}) := {
      toFun y := ⟨f y, fun he => hav y.prop (congrArg Subtype.val he)⟩
      map_rel' := fun h => f.map_adj h }
    exact K.prop ⟨(P.delete_vertex_colourable z).some.comap f'⟩

/-- Destruction of an odd component without a replacement strictly decreases
the exact number of bad components. No intermediate optimality is assumed. -/
theorem bad_count_strict_decrease (hΔ : ∀ v, H.degree v ≤ 2) (x : W)
    (heq : ∀ a b, a ≠ x → b ≠ x → (H.Adj a b ↔ J.Adj a b))
    (hold : ¬ (H.connectedComponentMk x).toSimpleGraph.Colorable 2)
    (hnew : (J.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    Fintype.card (BadComponent J) < Fintype.card (BadComponent H) := by
  have hav (K : BadComponent J) : x ∉ K.val.supp := by
    intro hx
    have he : J.connectedComponentMk x = K.val := (K.val.mem_supp_iff x).mp hx
    exact K.prop (he ▸ hnew)
  let f : BadComponent J → BadComponent H := fun K =>
    ⟨H.connectedComponentMk K.val.out,
      (bad_component_transfer H J hΔ x heq K (hav K)).1⟩
  have hfavoid (K : BadComponent J) : x ∉ (f K).val.supp :=
    (bad_component_transfer H J hΔ x heq K (hav K)).2
  have hfmem (K : BadComponent J) : K.val.out ∈ (f K).val.supp := by
    exact SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl
  have hinj : Function.Injective f := by
    intro K L hKL
    have he : (f K).val = (f L).val := congrArg Subtype.val hKL
    let C := (f K).val
    have hL : L.val.out ∈ C.supp := by
      change L.val.out ∈ (f K).val.supp
      rw [he]
      exact hfmem L
    let g : C.toSimpleGraph →g J := {
      toFun := Subtype.val
      map_rel' := fun {a b} h => (heq a b
        (fun hh => hfavoid K (hh ▸ a.prop))
        (fun hh => hfavoid K (hh ▸ b.prop))).mp h }
    have hr := ((C.connected_toSimpleGraph ⟨K.val.out,hfmem K⟩
      ⟨L.val.out,hL⟩).some.map g).reachable
    apply Subtype.ext
    have hh := SimpleGraph.ConnectedComponent.sound hr
    change J.connectedComponentMk K.val.out = J.connectedComponentMk L.val.out at hh
    exact K.val.out_eq.symm.trans (hh.trans L.val.out_eq)
  have hnotsurj : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨K,hK⟩ := hs ⟨H.connectedComponentMk x,hold⟩
    have he := congrArg Subtype.val hK
    apply hfavoid K
    rw [he]
    exact SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl
  exact Fintype.card_lt_of_injective_not_surjective f hinj hnotsurj

namespace Partition
variable {C : Type*} [Fintype C]

theorem phi2_eq_card_bad (π : W → C) :
    phi2 H π = Fintype.card (BadComponent (monochrome H π)) := by
  simp [phi2, BadComponent, Fintype.card_subtype]

/-- The odd-cycle conservation part of Lemma 4.3. A zero-cost flip at an odd
component creates another odd component through the moved vertex. -/
theorem flip_creates_odd_component {π : W → C} (hπ : MinimumTwo H π)
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2) (x : W) (j : C)
    (hzero : degreeIn H π x j = degreeIn H π x (π x))
    (hodd : ¬ ((monochrome H π).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ¬ ((monochrome H (Function.update π x j)).connectedComponentMk x).toSimpleGraph.Colorable 2 := by
  intro hn
  have hd : ∀ v, (monochrome H π).degree v ≤ 2 := by
    intro v
    have := hΔ v
    rw [← monochrome_degree] at this
    exact_mod_cast this
  have hlt := bad_count_strict_decrease (monochrome H π)
    (monochrome H (Function.update π x j)) hd x
    (by intro a b ha hb; simp [monochrome, Function.update_of_ne ha, Function.update_of_ne hb])
    hodd hn
  have hle := hπ.2 (Function.update π x j) (minimum_update H hπ.1 x j hzero)
  rw [phi2_eq_card_bad, phi2_eq_card_bad] at hle
  omega

end Partition

namespace Partition
variable {C : Type*} [Fintype C]

/-- The full even-path conclusion. The path is induced in the ambient graph,
is a whole component of the target class, and its ends are exactly the two
target-class neighbours of the vertex to be flipped. -/
structure EvenPathClosure (π : W → C) (e : W) (j : C) where
  size : ℕ
  two_le : 2 ≤ size
  even_size : Even size
  vertex : Fin size ↪ W
  in_class : ∀ i, π (vertex i) = j
  adj_iff : ∀ i k, H.Adj (vertex i) (vertex k) ↔ i.val+1 = k.val ∨ k.val+1 = i.val
  closed_in_class : ∀ i y, H.Adj (vertex i) y → π y = j → ∃ k, vertex k = y
  neighbours : ∀ y, H.Adj e y ∧ π y = j ↔
    ∃ i, vertex i = y ∧ (i.val = 0 ∨ i.val+1 = size)

/-- Extract the entire even target path from an odd component after a flip. -/
theorem even_path_of_flip_bad {π : W → C} (e : W) (j : C) (hj : j ≠ π e)
    (hbound : ∀ v, degreeIn H (Function.update π e j) v ((Function.update π e j) v) ≤ 2)
    (hbad : ¬ ((monochrome H (Function.update π e j)).connectedComponentMk e).toSimpleGraph.Colorable 2) :
    Nonempty (EvenPathClosure H π e j) := by
  let σ := Function.update π e j
  let M := monochrome H σ
  let K := M.connectedComponentMk e
  have hm : ∀ v, M.degree v ≤ 2 := by
    intro v
    have hh := hbound v
    rw [← monochrome_degree] at hh
    exact_mod_cast hh
  obtain ⟨P⟩ := component_pathCycleOrder M hm K
  obtain ⟨hc,ho⟩ := P.nonbipartite_closed_odd hbad
  let z : K.supp := ⟨e,(K.mem_supp_iff e).mpr rfl⟩
  let q := P.deleteCycleIso hc z
  let f : Fin (P.size-1) → W := fun i => (q i).val.val
  have hne (i) : f i ≠ e := fun he => (q i).prop (Subtype.ext he)
  have hclass (i) : π (f i) = j := by
    have hh := monochrome_class_constant H σ K (q i).val.prop z.prop
    change σ (f i) = σ e at hh
    simpa [σ, Function.update_of_ne (hne i)] using hh
  have hsurj {y : W} (hy : y ∈ K.supp) (hye : y ≠ e) : ∃ i, f i = y := by
    let y' : {x : K.supp // x ≠ z} := ⟨⟨y,hy⟩,fun he => hye (congrArg Subtype.val he)⟩
    exact ⟨q.symm y', congrArg (fun x => x.val.val) (q.apply_symm_apply y')⟩
  have hend (i) : H.Adj e (f i) ↔ i.val = 0 ∨ i.val+1 = P.size-1 := by
    have hh := P.deleteCycleIso_endpoints hc z i
    change (H.Adj e (f i) ∧ σ e = σ (f i)) ↔ _ at hh
    simpa [σ, Function.update_of_ne (hne i), hclass i] using hh
  have hsize := P.closed_size hc
  refine ⟨⟨P.size-1,by omega, ?_, ⟨f,?_⟩, hclass, ?_, ?_, ?_⟩⟩
  · rw [Nat.even_iff]
    have hh := Nat.odd_iff.mp ho
    omega
  · intro i k he
    apply q.injective
    apply Subtype.ext
    exact Subtype.ext he
  · intro i k
    change H.Adj (f i) (f k) ↔ _
    have hh := q.map_adj_iff (v := i) (w := k)
    change (H.Adj (f i) (f k) ∧ σ (f i) = σ (f k)) ↔ _ at hh
    simpa [σ, Function.update_of_ne (hne i), Function.update_of_ne (hne k),
      hclass i, hclass k, SimpleGraph.pathGraph_adj] using hh
  · intro i y hiy hy
    have hye : y ≠ e := fun he => hj (by simpa [he] using hy.symm)
    apply hsurj
    · apply K.mem_supp_of_adj_mem_supp (q i).val.prop
      refine ⟨hiy,?_⟩
      change σ (f i) = σ y
      simp [σ,Function.update_of_ne (hne i), Function.update_of_ne hye, hclass i,hy]
    · exact hye
  · intro y
    constructor
    · rintro ⟨hey,hy⟩
      have hye := hey.ne.symm
      have hyK : y ∈ K.supp := K.mem_supp_of_adj_mem_supp z.prop
        ⟨hey,by change σ e = σ y; simp [σ,Function.update_of_ne hye,hy]⟩
      obtain ⟨i,rfl⟩ := hsurj hyK hye
      exact ⟨i,rfl,(hend i).mp hey⟩
    · rintro ⟨i,rfl,hi⟩
      exact ⟨(hend i).mpr hi,hclass i⟩

/-- Lemma 4.3, valid for any number of classes whenever every primary minimum
has monochromatic degree at most two. This includes both nine and ten classes. -/
theorem zero_class_even_path {π : W → C} (hπ : MinimumTwo H π)
    (hbound : ∀ σ : W → C, Minimum H σ → ∀ v, degreeIn H σ v (σ v) ≤ 2)
    (e : W) (j : C) (hj : j ≠ π e)
    (hzero : degreeIn H π e j = degreeIn H π e (π e))
    (hodd : ¬ ((monochrome H π).connectedComponentMk e).toSimpleGraph.Colorable 2) :
    Nonempty (EvenPathClosure H π e j) :=
  even_path_of_flip_bad H e j hj
    (hbound _ (minimum_update H hπ.1 e j hzero))
    (flip_creates_odd_component H hπ (hbound π hπ.1) e j hzero hodd)

end Partition
end Se20Part
