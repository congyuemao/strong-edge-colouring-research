import Se20Part.Decomposition
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

noncomputable section
open scoped Classical
open SimpleGraph Finset
namespace Se20Part

/-- The disjoint union of the line graphs of the two degree-two factors. -/
def factorLine {V : Type*} (G : SimpleGraph V) (c : G.edgeSet → Fin 2) :
    SimpleGraph G.edgeSet where
  Adj e f := c e = c f ∧ e ≠ f ∧ ∃ v, v ∈ e.val ∧ v ∈ f.val
  symm := ⟨by rintro e f ⟨hc, hn, v, he, hf⟩; exact ⟨hc.symm, hn.symm, v, hf, he⟩⟩
  loopless := ⟨fun e h => h.2.1 rfl⟩

theorem factorLine_walk_color {V : Type*} {G : SimpleGraph V} {c : G.edgeSet → Fin 2}
    {e f : G.edgeSet} (p : (factorLine G c).Walk e f) :
    ∀ x ∈ p.support, c x = c e := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact (ih x hx).trans h.1.symm

def factorLineHom {V : Type*} {G : SimpleGraph V} (c : G.edgeSet → Fin 2)
    (a b : G.edgeSet → V)
    (he : ∀ e, G.Adj (a e) (b e) ∧ e.val = s(a e,b e))
    (ha : ∀ e f, c e = c f → a e = a f → e = f)
    (hb : ∀ e f, c e = c f → b e = b f → e = f) : factorLine G c →g G where
  toFun := a
  map_rel' := by
    rintro e f ⟨hc, hn, v, hv, hv'⟩
    rw [(he e).2, Sym2.mem_iff] at hv
    rw [(he f).2, Sym2.mem_iff] at hv'
    rcases hv with hv | hv <;> rcases hv' with hv' | hv'
    · exact (hn (ha e f hc (hv.symm.trans hv'))).elim
    · simpa only [← hv, hv'] using (he f).1.symm
    · simpa only [← hv, hv'] using (he e).1
    · exact (hn (hb e f hc (hv.symm.trans hv'))).elim

theorem factorLine_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : G.edgeSet → Fin 2) (a b : G.edgeSet → V)
    (he : ∀ e, G.Adj (a e) (b e) ∧ e.val = s(a e,b e))
    (ha : ∀ e f, c e = c f → a e = a f → e = f)
    (hb : ∀ e f, c e = c f → b e = b f → e = f) :
    DegreeLE (factorLine G c) 2 := by
  intro e
  have hshape (f : (factorLine G c).neighborSet e) :
      a f.val = b e ∨ b f.val = a e := by
    obtain ⟨hc, hn, v, hv, hv'⟩ := f.property
    rw [(he e).2, Sym2.mem_iff] at hv
    rw [(he f.val).2, Sym2.mem_iff] at hv'
    rcases hv with hv | hv <;> rcases hv' with hv' | hv'
    · exact (hn (ha e f.val hc (hv.symm.trans hv'))).elim
    · exact Or.inr (hv'.symm.trans hv)
    · exact Or.inl (hv'.symm.trans hv)
    · exact (hn (hb e f.val hc (hv.symm.trans hv'))).elim
  let f : (factorLine G c).neighborSet e → Bool :=
    fun x => decide (a x.val = b e)
  have hinj : Function.Injective f := by
    intro x y h
    have hc := x.property.1.symm.trans y.property.1
    apply Subtype.ext
    by_cases hx : a x.val = b e
    · have hy : a y.val = b e := by simpa [f, hx] using h.symm
      exact ha _ _ hc (hx.trans hy.symm)
    · have hy : a y.val ≠ b e := by simpa [f, hx] using h.symm
      exact hb _ _ hc ((hshape x).resolve_left hx |>.trans ((hshape y).resolve_left hy).symm)
  simpa using Nat.card_le_card_of_injective f hinj

theorem factorLine_girth {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : G.edgeSet → Fin 2) (a b : G.edgeSet → V)
    (he : ∀ e, G.Adj (a e) (b e) ∧ e.val = s(a e,b e))
    (ha : ∀ e f, c e = c f → a e = a f → e = f)
    (hb : ∀ e f, c e = c f → b e = b f → e = f)
    {g : ℕ} (hg : GirthAtLeast G g) : GirthAtLeast (factorLine G c) g := by
  intro e p hp
  let S : Set G.edgeSet := {f | c f = c e}
  let q := p.induce S (factorLine_walk_color p)
  have hq : q.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce S).toHom)
    simpa [q] using hp
  let φ := (factorLineHom c a b he ha hb).comp (Embedding.induce S).toHom
  have hinj : Function.Injective φ := by
    intro x y h
    exact Subtype.ext (ha x.val y.val (x.property.trans y.property.symm) h)
  have hind {x y : G.edgeSet} (w : (factorLine G c).Walk x y)
      (hw : ∀ z ∈ w.support, z ∈ S) : (w.induce S hw).length = w.length := by
    induction w with
    | nil => rfl
    | cons h w ih => simpa using ih _
  have hlen : q.length = p.length := hind p _
  have hh := hg _ (q.map φ) (hq.map hinj)
  simp only [Walk.length_map] at hh
  exact hh.trans_eq hlen

/-- A cycle in a maximum-degree-two graph is an entire connected component. -/
theorem cycle_component {X : Type*} [Fintype X] {H : SimpleGraph X}
    (hd : DegreeLE H 2) {v : X} {p : H.Walk v v} (hp : p.IsCycle) :
    ∃ C : H.ConnectedComponent, p.toSubgraph.verts = C.supp := by
  apply p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp
  intro w hw z hz
  have hcard := hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hw)
  have hle : (H.neighborSet w).ncard ≤ (p.toSubgraph.neighborSet w).ncard := by
    rw [hcard]
    simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using hd w
  have hs := Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset w) hle
  have hz' : z ∈ H.neighborSet w := hz
  rw [← hs] at hz'
  exact hz'

def CyclicComponent {X : Type*} (H : SimpleGraph X) :=
  {C : H.ConnectedComponent // ∃ v, ∃ p : H.Walk v v,
    p.IsCycle ∧ p.toSubgraph.verts = C.supp}

theorem cycle_support_card {X : Type*} [Fintype X] {H : SimpleGraph X}
    {v : X} {p : H.Walk v v} (hp : p.IsCycle) :
    Nat.card p.toSubgraph.verts = p.length := by
  have hs : p.toSubgraph.verts = {x | x ∈ p.support.tail} := by
    ext x
    rw [p.mem_verts_toSubgraph]
    constructor
    · intro hx
      rcases ((p.mem_support_iff).mp hx) with rfl | hx
      · exact Walk.end_mem_tail_support hp.not_nil
      · exact hx
    · exact List.mem_of_mem_tail
  rw [hs]
  change Nat.card {x // x ∈ p.support.tail} = p.length
  have eqv : {x // x ∈ p.support.tail} ≃ ↥p.support.tail.toFinset :=
    Equiv.subtypeEquivRight (by simp)
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hp.support_nodup]
  simp

theorem cyclicComponent_size {X : Type*} [Fintype X] {H : SimpleGraph X}
    {g : ℕ} (hg : GirthAtLeast H g) (C : CyclicComponent H) :
    g ≤ Nat.card C.val.supp := by
  obtain ⟨v, p, hp, hs⟩ := C.property
  rw [← hs, cycle_support_card hp]
  exact hg v p hp

theorem cycle_cut_forest {X : Type*} [Fintype X] {H : SimpleGraph X}
    (hd : DegreeLE H 2) (s : CyclicComponent H → X)
    (hs : ∀ C, s C ∈ C.val.supp) : (H.induce (Set.range s)ᶜ).IsAcyclic := by
  intro v p hp
  let φ : H.induce (Set.range s)ᶜ →g H := (Embedding.induce (Set.range s)ᶜ).toHom
  let q := p.map φ
  have hq : q.IsCycle := hp.map Subtype.val_injective
  obtain ⟨C, hC⟩ := cycle_component hd hq
  let C' : CyclicComponent H := ⟨C, v.val, q, hq, hC⟩
  have hm : s C' ∈ q.support := by
    rw [← q.mem_verts_toSubgraph, hC]
    exact hs C'
  simp only [q, Walk.support_map, List.mem_map] at hm
  obtain ⟨w, _, hw⟩ := hm
  exact w.property ⟨C', hw.symm⟩

/-- A uniform cycle-cutting variant of steps 2--3: one edge is removed from
every cycle component, including the even ones. This retains the same girth
threshold and gives forests, avoiding a separate alternating-even-cycle case. -/
theorem sparse_cycle_cut {V : Type} [Fintype V] {G : SimpleGraph V}
    (hax : Haxell) (hd : MaxDegreeFour G) (H : SimpleGraph G.edgeSet)
    (hdeg : DegreeLE H 2) (hg : GirthAtLeast H 39360) :
    ∃ D : Set G.edgeSet, Separated G 8 D ∧ (H.induce Dᶜ).IsAcyclic ∧
      ∀ C : CyclicComponent H, ∃! e, e ∈ D ∧ e ∈ C.val.supp := by
  let I := CyclicComponent H
  letI : Finite I := by unfold I CyclicComponent; infer_instance
  letI : Fintype I := Fintype.ofFinite I
  let E : Set G.edgeSet := {e | ∃ C : I, e ∈ C.val.supp}
  let part : E → I := fun e => e.property.choose
  have mempart (e : E) : e.val ∈ (part e).val.supp := e.property.choose_spec
  have parteq (e : E) (C : I) (h : e.val ∈ C.val.supp) : part e = C :=
    Subtype.ext (ConnectedComponent.eq_of_common_vertex (mempart e) h)
  have surj : Function.Surjective part := by
    intro C
    obtain ⟨e, he⟩ := C.val.nonempty_supp
    exact ⟨⟨e, C, he⟩, parteq _ C he⟩
  have hsize (C : I) : 39360 ≤ Nat.card {e // part e = C} := by
    let eqv : {e // part e = C} ≃ C.val.supp :=
      { toFun := fun e => ⟨e.val.val, by
          have hh := mempart e.val
          rwa [e.property] at hh⟩
        invFun := fun e => ⟨⟨e.val, C, e.property⟩, parteq _ C e.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact cyclicComponent_size hg C
  obtain ⟨s, hs, hsep⟩ := sparse_transversal_eight hax hd E part surj
    (fun C => by simpa only [← Nat.card_eq_fintype_card] using hsize C)
  let d : I → G.edgeSet := fun C => (s C).val
  have hdmem (C : I) : d C ∈ C.val.supp := by
    have := mempart (s C)
    rwa [hs C] at this
  refine ⟨Set.range d, ?_, cycle_cut_forest hdeg d hdmem, ?_⟩
  · rintro e ⟨C, rfl⟩ f ⟨C', rfl⟩ hne
    exact hsep C C' (fun h => hne (congrArg d h))
  · intro C
    refine ⟨d C, ⟨⟨C, rfl⟩, hdmem C⟩, ?_⟩
    rintro e ⟨⟨C', rfl⟩, he⟩
    have : C' = C := Subtype.ext (ConnectedComponent.eq_of_common_vertex (hdmem C') he)
    exact congrArg d this

theorem four_matchings_of_factor_forest {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : G.edgeSet → Fin 2) (D : Set G.edgeSet)
    (hf : ((factorLine G c).induce Dᶜ).IsAcyclic) :
    ∃ M : Fin 4 → Set G.edgeSet, (∀ i, IsMatching (M i)) ∧
      (∀ e, e ∈ D ∨ ∃ i, e ∈ M i) ∧ (∀ i, Disjoint D (M i)) := by
  let q := hf.coloringTwo
  let color : ↥(Dᶜ) → Fin 4 := fun e => finProdFinEquiv (c e.val, q e)
  let M : Fin 4 → Set G.edgeSet := fun i => {e | ∃ he : e ∉ D, color ⟨e, he⟩ = i}
  refine ⟨M, ?_, ?_, ?_⟩
  · intro i e ⟨he, hce⟩ f ⟨hf', hcf⟩ v hve hvf
    by_contra hne
    have hh := finProdFinEquiv.injective (hce.trans hcf.symm)
    have hc : c e = c f := congrArg Prod.fst hh
    have hq : q ⟨e, he⟩ = q ⟨f, hf'⟩ := congrArg Prod.snd hh
    exact q.valid (show ((factorLine G c).induce Dᶜ).Adj ⟨e, he⟩ ⟨f, hf'⟩ from
      ⟨hc, hne, v, hve, hvf⟩) hq
  · intro e
    by_cases he : e ∈ D
    · exact Or.inl he
    · exact Or.inr ⟨color ⟨e, he⟩, he, rfl⟩
  · intro i
    exact Set.disjoint_left.mpr (fun e he ⟨hn, _⟩ => hn he)

/-- Steps 1--3 of Theorem B, with the all-cycle-cut variant made explicit. -/
theorem sparse_four_matching_cover {V : Type} [Fintype V] (hax : Haxell)
    {G : SimpleGraph V} (hd : MaxDegreeFour G) (hg : GirthAtLeast G 39360) :
    ∃ (D : Set G.edgeSet) (M : Fin 4 → Set G.edgeSet),
      Separated G 8 D ∧ (∀ i, IsMatching (M i)) ∧
      (∀ e, e ∈ D ∨ ∃ i, e ∈ M i) ∧ (∀ i, Disjoint D (M i)) := by
  obtain ⟨c, a, b, he, ha, hb⟩ := directed_two_degree_decomposition G hd
  obtain ⟨D, hs, hf, _⟩ := sparse_cycle_cut hax hd (factorLine G c)
    (factorLine_degree c a b he ha hb) (factorLine_girth c a b he ha hb hg)
  obtain ⟨M, hm, hcover, hdisj⟩ := four_matchings_of_factor_forest c D hf
  exact ⟨D, M, hs, hm, hcover, hdisj⟩

theorem sparse_cycle_cut_general {V : Type} [Fintype V] {G : SimpleGraph V}
    (hax : Haxell) (hd : MaxDegreeFour G) (H : SimpleGraph G.edgeSet)
    (hdeg : DegreeLE H 2) (k g : ℕ) (hg : GirthAtLeast H g)
    (hbound : 2*(3^(k+2)-3) ≤ g) :
    ∃ D : Set G.edgeSet, Separated G (k+1) D ∧ (H.induce Dᶜ).IsAcyclic := by
  let I := CyclicComponent H
  letI : Finite I := by unfold I CyclicComponent; infer_instance
  letI : Fintype I := Fintype.ofFinite I
  let E : Set G.edgeSet := {e | ∃ C : I, e ∈ C.val.supp}
  let part : E → I := fun e => e.property.choose
  have mempart (e : E) : e.val ∈ (part e).val.supp := e.property.choose_spec
  have parteq (e : E) (C : I) (h : e.val ∈ C.val.supp) : part e = C :=
    Subtype.ext (ConnectedComponent.eq_of_common_vertex (mempart e) h)
  have surj : Function.Surjective part := by
    intro C
    obtain ⟨e,he⟩ := C.val.nonempty_supp
    exact ⟨⟨e,C,he⟩,parteq _ C he⟩
  have hsize (C : I) : 2*(3^(k+2)-3) ≤ Nat.card {e // part e = C} := by
    let eqv : {e // part e = C} ≃ C.val.supp :=
      { toFun := fun e => ⟨e.val.val,by have hh := mempart e.val; rwa [e.property] at hh⟩
        invFun := fun e => ⟨⟨e.val,C,e.property⟩,parteq _ C e.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact hbound.trans (cyclicComponent_size hg C)
  obtain ⟨s,hs,hsep⟩ := sparse_transversal hax hd E part surj k
    (fun C => by simpa only [← Nat.card_eq_fintype_card] using hsize C)
  let d : I → G.edgeSet := fun C => (s C).val
  have hdmem (C : I) : d C ∈ C.val.supp := by
    have := mempart (s C)
    rwa [hs C] at this
  refine ⟨Set.range d,?_,cycle_cut_forest hdeg d hdmem⟩
  rintro e ⟨C,rfl⟩ f ⟨C',rfl⟩ hne
  simpa only [Nat.add_sub_cancel] using hsep C C' (fun h => hne (congrArg d h))

theorem sparse_four_matching_cover_five {V : Type} [Fintype V] (hax : Haxell)
    {G : SimpleGraph V} (hd : MaxDegreeFour G) (hg : GirthAtLeast G 1452) :
    ∃ (D : Set G.edgeSet) (M : Fin 4 → Set G.edgeSet),
      Separated G 5 D ∧ (∀ i, IsMatching (M i)) ∧
      (∀ e, e ∈ D ∨ ∃ i, e ∈ M i) ∧ (∀ i, Disjoint D (M i)) := by
  obtain ⟨c,a,b,he,ha,hb⟩ := directed_two_degree_decomposition G hd
  obtain ⟨D,hs,hf⟩ := sparse_cycle_cut_general hax hd (factorLine G c)
    (factorLine_degree c a b he ha hb) 4 1452 (factorLine_girth c a b he ha hb hg) (by decide)
  obtain ⟨M,hm,hcover,hdisj⟩ := four_matchings_of_factor_forest c D hf
  exact ⟨D,M,hs,hm,hcover,hdisj⟩

end Se20Part
