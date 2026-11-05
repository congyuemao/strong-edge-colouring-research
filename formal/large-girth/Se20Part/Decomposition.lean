import Se20Part.OpenStatements
import Mathlib.Combinatorics.Hall.Finite

noncomputable section
open scoped Classical
open Finset
namespace Se20Part

/-- Counting a union of equally sized fibers. -/
theorem uniform_fiber_count {X A : Type*} [Fintype X] [Fintype A]
    (f : X → A) (k : ℕ) (hf : ∀ a, Nat.card {x // f x = a} = k)
    (s : Finset A) : (univ.filter fun x => f x ∈ s).card = s.card * k := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  simp only [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hf, sum_const, smul_eq_mul]

/-- Hall's theorem, with its condition proved by counting the two uniform fibers.
This formulation permits parallel edges. -/
theorem uniform_bipartite_matching {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    (f : X → A) (g : X → B) {k : ℕ} (hk : 0 < k)
    (hf : ∀ a, Nat.card {x // f x = a} = k)
    (hg : ∀ b, Nat.card {x // g x = b} = k) :
    ∃ q : A → X, (∀ a, f (q a) = a) ∧ Function.Bijective (g ∘ q) := by
  let t : A → Finset B := fun a => (univ.filter fun x => f x = a).image g
  have hall : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    have sub : (univ.filter fun x => f x ∈ s) ⊆
        (univ.filter fun x => g x ∈ s.biUnion t) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact mem_biUnion.mpr ⟨f x, hx, mem_image.mpr ⟨x, by simp, rfl⟩⟩
    have hc := card_le_card sub
    rw [uniform_fiber_count f k hf, uniform_fiber_count g k hg] at hc
    exact Nat.le_of_mul_le_mul_right hc hk
  obtain ⟨b, hb, hbt⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hex : ∀ a, ∃ x, f x = a ∧ g x = b a := by
    intro a
    obtain ⟨x, hx, hxb⟩ := mem_image.mp (hbt a)
    exact ⟨x, (mem_filter.mp hx).2, hxb⟩
  choose q hqf hqg using hex
  refine ⟨q, hqf, ?_⟩
  have eqb : g ∘ q = b := funext hqg
  rw [eqb]
  have hcard : Fintype.card A = Fintype.card B := by
    have ha := uniform_fiber_count f k hf univ
    have hb' := uniform_fiber_count g k hg univ
    simp only [mem_univ, filter_true, card_univ] at ha hb'
    exact Nat.eq_of_mul_eq_mul_right hk (ha.symm.trans hb')
  exact ⟨hb, (Fintype.bijective_iff_injective_and_card b).mpr ⟨hb, hcard⟩ |>.surjective⟩

/-- A regular incidence structure has an orientation with two outgoing edges per vertex.
The vertices in the right part are duplicated, and the Hall condition is just 4 = 4. -/
theorem regular_four_orientation {E V : Type*} [Fintype E] [Fintype V]
    (R : E → V → Prop)
    (he : ∀ e, Nat.card {v // R e v} = 2)
    (hv : ∀ v, Nat.card {e // R e v} = 4) :
    ∃ b : E ≃ V × Fin 2, ∀ e, R e (b e).1 := by
  let X := {p : E × (V × Fin 2) // R p.1 p.2.1}
  let f : X → E := fun x => x.val.1
  let g : X → V × Fin 2 := fun x => x.val.2
  have hf (e : E) : Nat.card {x // f x = e} = 4 := by
    let eqv : {x // f x = e} ≃ ({v // R e v} × Fin 2) :=
      { toFun := fun x => (⟨x.val.val.2.1, by
            have := x.val.property
            simpa only [← x.property] using this⟩, x.val.val.2.2)
        invFun := fun x => ⟨⟨(e, x.1.val, x.2), x.1.property⟩, rfl⟩
        left_inv := by rintro ⟨⟨⟨a, v, i⟩, h⟩, h'⟩; dsimp [f] at h'; subst a; rfl
        right_inv := by intro x; rfl }
    rw [Nat.card_congr eqv, Nat.card_prod, he]
    norm_num
  have hg (v : V × Fin 2) : Nat.card {x // g x = v} = 4 := by
    let eqv : {x // g x = v} ≃ {e // R e v.1} :=
      { toFun := fun x => ⟨x.val.val.1, by
            have := x.val.property
            simpa only [← x.property] using this⟩
        invFun := fun x => ⟨⟨(x.val, v), x.property⟩, rfl⟩
        left_inv := by rintro ⟨⟨⟨a, w⟩, h⟩, h'⟩; dsimp [g] at h'; subst w; rfl
        right_inv := by intro x; rfl }
    rw [Nat.card_congr eqv, hv]
  obtain ⟨q, hq, hbij⟩ := uniform_bipartite_matching f g (by decide : 0 < 4)
    (fun e => by simpa using hf e) (fun v => by simpa using hg v)
  refine ⟨Equiv.ofBijective (g ∘ q) hbij, ?_⟩
  intro e
  have := (q e).property
  change R e (g (q e)).1
  change R (f (q e)) (g (q e)).1 at this
  rwa [hq e] at this

theorem other_of_card_two {V : Type*} [Fintype V] (P : V → Prop)
    (hc : Nat.card {v // P v} = 2) (v : V) (hv : P v) :
    ∃ w, v ≠ w ∧ ∀ x, P x ↔ x = v ∨ x = w := by
  have hc' : (univ.filter P).card = 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc'
  have hh (x : V) : P x ↔ x = a ∨ x = b := by
    have := congrArg (fun s : Finset V => x ∈ s) hs
    simpa using this
  rcases (hh v).mp hv with rfl | rfl
  · exact ⟨b, hab, hh⟩
  · exact ⟨a, hab.symm, fun x => (hh x).trans or_comm⟩

theorem card_or_disjoint {X : Type*} [Fintype X] (P Q : X → Prop)
    (hd : ∀ x, P x → Q x → False) :
    Nat.card {x // P x ∨ Q x} =
      Nat.card {x // P x} + Nat.card {x // Q x} := by
  simp only [Nat.card_eq_fintype_card]
  apply Fintype.card_subtype_or_disjoint
  exact fun s hp hq x hx => False.elim (hd x (hp x hx) (hq x hx))

/-- The second Hall application is the degree-two case of König, proved here
for an incidence multigraph rather than imported as a literature hypothesis. -/
theorem two_fiber_coloring {E V : Type*} [Fintype E] [Fintype V]
    (a b : E → V)
    (ha : ∀ v, Nat.card {e // a e = v} = 2)
    (hb : ∀ v, Nat.card {e // b e = v} = 2) :
    ∃ c : E → Fin 2, ∀ i v,
      Nat.card {e // c e = i ∧ (a e = v ∨ b e = v)} ≤ 2 := by
  obtain ⟨q, hqa, hqb⟩ := uniform_bipartite_matching a b (by decide : 0 < 2) ha hb
  let S : Set E := Set.range q
  have qinj : Function.Injective q := by
    intro x y h
    simpa only [hqa] using congrArg a h
  have uniqueA (v : V) : ∃! e, e ∈ S ∧ a e = v := by
    refine ⟨q v, ⟨⟨v, rfl⟩, hqa v⟩, ?_⟩
    rintro e ⟨⟨w, rfl⟩, hw⟩
    simpa only [hqa] using congrArg q (by simpa only [hqa] using hw)
  have uniqueB (v : V) : ∃! e, e ∈ S ∧ b e = v := by
    obtain ⟨w, hw⟩ := hqb.surjective v
    refine ⟨q w, ⟨⟨w, rfl⟩, hw⟩, ?_⟩
    rintro e ⟨⟨z, rfl⟩, hz⟩
    exact congrArg q (hqb.injective (hz.trans hw.symm))
  have split (f : E → V) (hf : ∀ v, Nat.card {e // f e = v} = 2)
      (hu : ∀ v, ∃! e, e ∈ S ∧ f e = v) (i : Fin 2) (v : V) :
      Nat.card {e // (if e ∈ S then (0 : Fin 2) else 1) = i ∧ f e = v} ≤ 1 := by
    have hone : Nat.card {e // e ∈ S ∧ f e = v} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
      obtain ⟨e, he, hue⟩ := hu v
      exact ⟨⟨e, he⟩, fun y => Subtype.ext (hue y.val y.property)⟩
    have hsum := card_or_disjoint (fun e => e ∈ S ∧ f e = v)
      (fun e => e ∉ S ∧ f e = v) (by aesop)
    have heq : {e | (e ∈ S ∧ f e = v) ∨ (e ∉ S ∧ f e = v)} =
        {e | f e = v} := by ext e; simp only [Set.mem_ofPred_eq]; tauto
    change Nat.card ↥{e | (e ∈ S ∧ f e = v) ∨ (e ∉ S ∧ f e = v)} = _ at hsum
    rw [heq] at hsum
    change Nat.card {e // f e = v} = _ at hsum
    rw [hf v, hone] at hsum
    fin_cases i
    · simpa using hone.le
    · have : Nat.card {e // e ∉ S ∧ f e = v} ≤ 1 := by omega
      simpa using this
  refine ⟨fun e => if e ∈ S then 0 else 1, fun i v => ?_⟩
  have heq : {e | (if e ∈ S then (0 : Fin 2) else 1) = i ∧ (a e = v ∨ b e = v)} =
      {e | ((if e ∈ S then (0 : Fin 2) else 1) = i ∧ a e = v) ∨
        ((if e ∈ S then (0 : Fin 2) else 1) = i ∧ b e = v)} := by
    ext e; simp only [Set.mem_ofPred_eq]; tauto
  change Nat.card ↥{e | (if e ∈ S then (0 : Fin 2) else 1) = i ∧ (a e = v ∨ b e = v)} ≤ 2
  rw [heq]
  have hle := Fintype.card_subtype_or
    (fun e => (if e ∈ S then (0 : Fin 2) else 1) = i ∧ a e = v)
    (fun e => (if e ∈ S then (0 : Fin 2) else 1) = i ∧ b e = v)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hle
  exact hle.trans (by
    have := split a ha uniqueA i v
    have := split b hb uniqueB i v
    omega)

/-- Every finite loopless 4-regular incidence multigraph splits into two
subgraphs of maximum degree two. Both matching arguments are kernel proofs. -/
theorem regular_four_split {E V : Type*} [Fintype E] [Fintype V]
    (R : E → V → Prop)
    (he : ∀ e, Nat.card {v // R e v} = 2)
    (hv : ∀ v, Nat.card {e // R e v} = 4) :
    ∃ c : E → Fin 2, ∀ i v, Nat.card {e // c e = i ∧ R e v} ≤ 2 := by
  obtain ⟨o, ho⟩ := regular_four_orientation R he hv
  let a : E → V := fun e => (o e).1
  have ha (v : V) : Nat.card {e // a e = v} = 2 := by
    let eqv : {e // a e = v} ≃ Fin 2 :=
      { toFun := fun e => (o e.val).2
        invFun := fun i => ⟨o.symm (v, i), by simp [a]⟩
        left_inv := by
          intro e
          apply Subtype.ext
          apply o.injective
          simp only [Equiv.apply_symm_apply]
          exact Prod.ext e.property.symm rfl
        right_inv := by intro i; simp }
    simpa using Nat.card_congr eqv
  choose b hab hr using fun e => other_of_card_two (R e) (he e) (a e) (ho e)
  have hb (v : V) : Nat.card {e // b e = v} = 2 := by
    have hs := card_or_disjoint (fun e => a e = v) (fun e => b e = v)
      (fun e h₁ h₂ => hab e (h₁.trans h₂.symm))
    have heq : {e | a e = v ∨ b e = v} = {e | R e v} := by
      ext e
      simp only [Set.mem_ofPred_eq, hr, eq_comm]
    change Nat.card ↥{e | a e = v ∨ b e = v} = _ at hs
    rw [heq] at hs
    change Nat.card {e // R e v} = _ at hs
    rw [hv v, ha v] at hs
    omega
  obtain ⟨c, hc⟩ := two_fiber_coloring a b ha hb
  refine ⟨c, fun i v => ?_⟩
  simpa only [hr, eq_comm] using hc i v

theorem incident_card {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Nat.card {e : G.edgeSet // v ∈ e.val} = G.degree v := by
  let eqv : {e : G.edgeSet // v ∈ e.val} ≃ G.incidenceSet v :=
    { toFun := fun e => ⟨e.val.val, e.val.property, e.property⟩
      invFun := fun e => ⟨⟨e.val, e.property.1⟩, e.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, G.card_incidenceSet_eq_degree]

theorem edge_endpoints_card {V : Type*} [Fintype V] (G : SimpleGraph V) (e : G.edgeSet) :
    Nat.card {v // v ∈ e.val} = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : univ.filter (fun v => v ∈ e.val) = e.val.toFinset := by
    ext v; simp [Sym2.mem_toFinset]
  rw [heq]
  exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)

/-- Complete to a loopless 4-regular multigraph by taking two copies and
joining corresponding vertices with one edge for each missing incidence. -/
def completionIncidence {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ((G.edgeSet × Bool) ⊕ (Σ v, Fin (4 - G.degree v))) → (V × Bool) → Prop
  | .inl (e, b), (v, b') => v ∈ e.val ∧ b = b'
  | .inr p, (v, _) => p.1 = v

theorem completion_edge_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : (G.edgeSet × Bool) ⊕ (Σ v, Fin (4 - G.degree v))) :
    Nat.card {v // completionIncidence G e v} = 2 := by
  rcases e with ⟨e, b⟩ | ⟨v, i⟩
  · let eqv : {v // completionIncidence G (.inl (e, b)) v} ≃ {v // v ∈ e.val} :=
      { toFun := fun v => ⟨v.val.1, v.property.1⟩
        invFun := fun v => ⟨(v.val, b), v.property, rfl⟩
        left_inv := by rintro ⟨⟨v, b'⟩, hv, hb⟩; subst b'; rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv, edge_endpoints_card]
  · let eqv : {w // completionIncidence G (.inr ⟨v, i⟩) w} ≃ Bool :=
      { toFun := fun w => w.val.2
        invFun := fun b => ⟨(v, b), rfl⟩
        left_inv := by rintro ⟨⟨w, b⟩, h⟩; dsimp [completionIncidence] at h; subst w; rfl
        right_inv := fun _ => rfl }
    simpa using Nat.card_congr eqv

theorem completion_vertex_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hd : MaxDegreeFour G) (v : V × Bool) :
    Nat.card {e // completionIncidence G e v} = 4 := by
  let eqv₁ : {e : G.edgeSet × Bool // completionIncidence G (.inl e) v} ≃
      {e : G.edgeSet // v.1 ∈ e.val} :=
    { toFun := fun e => ⟨e.val.1, e.property.1⟩
      invFun := fun e => ⟨(e.val, v.2), e.property, rfl⟩
      left_inv := by rintro ⟨⟨e, b⟩, he, hb⟩; subst b; rfl
      right_inv := fun _ => rfl }
  let eqv₂ : {e : (Σ w, Fin (4 - G.degree w)) // completionIncidence G (.inr e) v} ≃
      Fin (4 - G.degree v.1) :=
    { toFun := fun e => ⟨e.val.2.val, by
          have hi := e.val.2.isLt
          have h : e.val.1 = v.1 := e.property
          have hn := congrArg (fun w => 4 - G.degree w) h
          omega⟩
      invFun := fun i => ⟨⟨v.1, i⟩, rfl⟩
      left_inv := by rintro ⟨⟨w, i⟩, h⟩; dsimp [completionIncidence] at h; subst w; rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (Equiv.subtypeSum.trans (Equiv.sumCongr eqv₁ eqv₂)), Nat.card_sum,
    incident_card, Nat.card_fin]
  exact Nat.add_sub_of_le (hd v.1)

/-- Theorem B, step 1. A degree-four completion and two proved Hall arguments
replace the Euler-tour construction. There are no literature hypotheses. -/
theorem two_degree_decomposition : TwoDegreeDecompositionStatement := by
  intro V _ G hd
  obtain ⟨c, hc⟩ := regular_four_split (completionIncidence G)
    (completion_edge_card G) (completion_vertex_card G hd)
  refine ⟨fun e => c (.inl (e, false)), fun i v => ?_⟩
  let emb : {e : G.edgeSet // c (.inl (e, false)) = i ∧ v ∈ e.val} →
      {e // c e = i ∧ completionIncidence G e (v, false)} := fun e =>
    ⟨.inl (e.val, false), e.property.1, e.property.2, rfl⟩
  have hinj : Function.Injective emb := by
    intro e f h
    exact Subtype.ext (Prod.mk.inj (Sum.inl.inj (congrArg Subtype.val h))).1
  exact (Nat.card_le_card_of_injective emb hinj).trans (hc i (v, false))

theorem two_fiber_color_bounds {E V : Type*} [Fintype E] [Fintype V]
    (a b : E → V)
    (ha : ∀ v, Nat.card {e // a e = v} = 2)
    (hb : ∀ v, Nat.card {e // b e = v} = 2) :
    ∃ c : E → Fin 2, ∀ i v,
      Nat.card {e // c e = i ∧ a e = v} ≤ 1 ∧
      Nat.card {e // c e = i ∧ b e = v} ≤ 1 := by
  obtain ⟨q, hqa, hqb⟩ := uniform_bipartite_matching a b (by decide : 0 < 2) ha hb
  let S : Set E := Set.range q
  have uniqueA (v : V) : ∃! e, e ∈ S ∧ a e = v := by
    refine ⟨q v, ⟨⟨v, rfl⟩, hqa v⟩, ?_⟩
    rintro e ⟨⟨w, rfl⟩, hw⟩
    exact congrArg q (by simpa only [hqa] using hw)
  have uniqueB (v : V) : ∃! e, e ∈ S ∧ b e = v := by
    obtain ⟨w, hw⟩ := hqb.surjective v
    refine ⟨q w, ⟨⟨w, rfl⟩, hw⟩, ?_⟩
    rintro e ⟨⟨z, rfl⟩, hz⟩
    exact congrArg q (hqb.injective (hz.trans hw.symm))
  have split (f : E → V) (hf : ∀ v, Nat.card {e // f e = v} = 2)
      (hu : ∀ v, ∃! e, e ∈ S ∧ f e = v) (i : Fin 2) (v : V) :
      Nat.card {e // (if e ∈ S then (0 : Fin 2) else 1) = i ∧ f e = v} ≤ 1 := by
    have hone : Nat.card {e // e ∈ S ∧ f e = v} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
      obtain ⟨e, he, hue⟩ := hu v
      exact ⟨⟨e, he⟩, fun y => Subtype.ext (hue y.val y.property)⟩
    have hsum := card_or_disjoint (fun e => e ∈ S ∧ f e = v)
      (fun e => e ∉ S ∧ f e = v) (by aesop)
    have heq : {e | (e ∈ S ∧ f e = v) ∨ (e ∉ S ∧ f e = v)} =
        {e | f e = v} := by ext e; simp only [Set.mem_ofPred_eq]; tauto
    change Nat.card ↥{e | (e ∈ S ∧ f e = v) ∨ (e ∉ S ∧ f e = v)} = _ at hsum
    rw [heq] at hsum
    change Nat.card {e // f e = v} = _ at hsum
    rw [hf v, hone] at hsum
    fin_cases i
    · simpa using hone.le
    · have : Nat.card {e // e ∉ S ∧ f e = v} ≤ 1 := by omega
      simpa using this
  exact ⟨fun e => if e ∈ S then 0 else 1, fun i v =>
    ⟨split a ha uniqueA i v, split b hb uniqueB i v⟩⟩

theorem regular_four_directed_split {E V : Type*} [Fintype E] [Fintype V]
    (R : E → V → Prop)
    (he : ∀ e, Nat.card {v // R e v} = 2)
    (hv : ∀ v, Nat.card {e // R e v} = 4) :
    ∃ (c : E → Fin 2) (a b : E → V),
      (∀ e, a e ≠ b e ∧ ∀ v, R e v ↔ v = a e ∨ v = b e) ∧
      (∀ e f, c e = c f → a e = a f → e = f) ∧
      (∀ e f, c e = c f → b e = b f → e = f) := by
  obtain ⟨o, ho⟩ := regular_four_orientation R he hv
  let a : E → V := fun e => (o e).1
  have ha (v : V) : Nat.card {e // a e = v} = 2 := by
    let eqv : {e // a e = v} ≃ Fin 2 :=
      { toFun := fun e => (o e.val).2
        invFun := fun i => ⟨o.symm (v, i), by simp [a]⟩
        left_inv := by
          intro e
          apply Subtype.ext
          apply o.injective
          simp only [Equiv.apply_symm_apply]
          exact Prod.ext e.property.symm rfl
        right_inv := by intro i; simp }
    simpa using Nat.card_congr eqv
  choose b hab hr using fun e => other_of_card_two (R e) (he e) (a e) (ho e)
  have hb (v : V) : Nat.card {e // b e = v} = 2 := by
    have hs := card_or_disjoint (fun e => a e = v) (fun e => b e = v)
      (fun e h₁ h₂ => hab e (h₁.trans h₂.symm))
    have heq : {e | a e = v ∨ b e = v} = {e | R e v} := by
      ext e; simp only [Set.mem_ofPred_eq, hr, eq_comm]
    change Nat.card ↥{e | a e = v ∨ b e = v} = _ at hs
    rw [heq] at hs
    change Nat.card {e // R e v} = _ at hs
    rw [hv v, ha v] at hs
    omega
  obtain ⟨c, hc⟩ := two_fiber_color_bounds a b ha hb
  have uniq (f : E → V) (hf : ∀ i v, Nat.card {e // c e = i ∧ f e = v} ≤ 1)
      (e e' : E) (he : c e = c e') (hv : f e = f e') : e = e' := by
    have hh := hf (c e') (f e')
    rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff] at hh
    exact congrArg Subtype.val (hh ⟨e, he, hv⟩ ⟨e', rfl, rfl⟩)
  exact ⟨c, a, b, fun e => ⟨hab e, hr e⟩,
    uniq a (fun i v => (hc i v).1), uniq b (fun i v => (hc i v).2)⟩

/-- A version of step 1 that retains the orientation needed for the next step. -/
theorem directed_two_degree_decomposition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hd : MaxDegreeFour G) :
    ∃ (c : G.edgeSet → Fin 2) (a b : G.edgeSet → V),
      (∀ e, G.Adj (a e) (b e) ∧ e.val = s(a e, b e)) ∧
      (∀ e f, c e = c f → a e = a f → e = f) ∧
      (∀ e f, c e = c f → b e = b f → e = f) := by
  obtain ⟨c, a, b, hr, ha, hb⟩ := regular_four_directed_split (completionIncidence G)
    (completion_edge_card G) (completion_vertex_card G hd)
  let lift (e : G.edgeSet) : (G.edgeSet × Bool) ⊕ (Σ v, Fin (4-G.degree v)) :=
    .inl (e, false)
  have hea (e : G.edgeSet) : (a (lift e)).1 ∈ e.val ∧ (a (lift e)).2 = false := by
    have := ((hr (lift e)).2 (a (lift e))).mpr (Or.inl rfl)
    exact ⟨this.1, this.2.symm⟩
  have heb (e : G.edgeSet) : (b (lift e)).1 ∈ e.val ∧ (b (lift e)).2 = false := by
    have := ((hr (lift e)).2 (b (lift e))).mpr (Or.inr rfl)
    exact ⟨this.1, this.2.symm⟩
  have hab (e : G.edgeSet) : (a (lift e)).1 ≠ (b (lift e)).1 := by
    intro h
    exact (hr (lift e)).1 (Prod.ext h ((hea e).2.trans (heb e).2.symm))
  refine ⟨fun e => c (lift e), fun e => (a (lift e)).1, fun e => (b (lift e)).1,
    fun e => ?_, ?_, ?_⟩
  · have he := (Sym2.mem_and_mem_iff (hab e)).mp ⟨(hea e).1, (heb e).1⟩
    exact ⟨by simpa [he] using e.property, he⟩
  · intro e f hc he
    exact (Prod.mk.inj (Sum.inl.inj (ha (lift e) (lift f) hc
      (Prod.ext he ((hea e).2.trans (hea f).2.symm))))).1
  · intro e f hc he
    exact (Prod.mk.inj (Sum.inl.inj (hb (lift e) (lift f) hc
      (Prod.ext he ((heb e).2.trans (heb f).2.symm))))).1

end Se20Part

