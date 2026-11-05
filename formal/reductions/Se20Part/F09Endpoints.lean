import Se20Part.F01
import Se20Part.Triangle

noncomputable section
open scoped Classical
namespace Se20Part

namespace GirthFive
variable {V : Type*} {G : SimpleGraph V}

/-- The four possible witness edges between two disjoint selected edges. -/
def Cross (a b c d : V) : Prop :=
  G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

theorem Cross.flipLeft {a b c d : V} (h : Cross (G := G) a b c d) :
    Cross (G := G) b a c d := by
  unfold Cross at h ⊢
  tauto

theorem Cross.flipRight {a b c d : V} (h : Cross (G := G) a b c d) :
    Cross (G := G) a b d c := by
  unfold Cross at h ⊢
  tauto

theorem Cross.symm {a b c d : V} (h : Cross (G := G) a b c d) :
    Cross (G := G) c d a b := by
  rcases h with h|h|h|h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem cross_of_conflict {a b c d : V} (e f : G.edgeSet)
    (he : e.val = s(a,b)) (hf : f.val = s(c,d))
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : (L2 G).Adj e f) : Cross (G := G) a b c d := by
  obtain ⟨_,x,hx,y,hy,hxy⟩ := h
  rw [he, Sym2.mem_iff] at hx
  rw [hf, Sym2.mem_iff] at hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
    rcases hxy with hxy|hxy <;> simp_all [Cross]

theorem cross_of_clique {a b c d : V} (e f : G.edgeSet)
    (he : e.val = s(a,b)) (hf : f.val = s(c,d))
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    {Q : Finset G.edgeSet} (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (heQ : e ∈ Q) (hfQ : f ∈ Q) : Cross (G := G) a b c d := by
  apply cross_of_conflict e f he hf hac had hbc hbd
  apply hQ heQ hfQ
  intro h
  have hm : a ∈ f.val := h ▸ (he ▸ Sym2.mem_mk_left a b)
  rw [hf, Sym2.mem_iff] at hm
  exact hm.elim hac had

set_option maxHeartbeats 1000000 in
/-- F09, endpoint lemma 1.1. The six vertices are distinct; omitting that
condition would make the assertion false. All four conflicts are ambient. -/
theorem disjoint_two_paths_centres (hg : 5 ≤ G.egirth)
    (v : Fin 6 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4)) (h45 : G.Adj (v 4) (v 5))
    (h03 : Cross (G := G) (v 0) (v 1) (v 3) (v 4))
    (h04 : Cross (G := G) (v 0) (v 1) (v 4) (v 5))
    (h13 : Cross (G := G) (v 1) (v 2) (v 3) (v 4))
    (h14 : Cross (G := G) (v 1) (v 2) (v 4) (v 5)) :
    G.Adj (v 1) (v 4) := by
  have ns (a b c d : Fin 6) (hac : a ≠ c) (hbd : b ≠ d)
      (hab : G.Adj (v a) (v b)) (hbc : G.Adj (v b) (v c))
      (hcd : G.Adj (v c) (v d)) (hda : G.Adj (v d) (v a)) : False := by
    rcases square_backtrack hg hab hbc hcd hda with h|h
    · exact hac (hv h)
    · exact hbd (hv h)
  by_contra hn
  unfold Cross at h03 h04 h13 h14
  have hn13 : ¬ G.Adj (v 1) (v 3) := by
    intro h
    have hn15 : ¬ G.Adj (v 1) (v 5) :=
      fun hh => ns 1 3 4 5 (by decide) (by decide) h h34 h45 hh.symm
    have hn04 : ¬ G.Adj (v 0) (v 4) :=
      fun hh => ns 0 1 3 4 (by decide) (by decide) h01 h h34 hh.symm
    have hn24 : ¬ G.Adj (v 2) (v 4) :=
      fun hh => ns 2 1 3 4 (by decide) (by decide) h12.symm h h34 hh.symm
    have h05 : G.Adj (v 0) (v 5) := (h04.resolve_left hn04).resolve_right (not_or.mpr ⟨hn,hn15⟩)
    have h25 : G.Adj (v 2) (v 5) := ((h14.resolve_left hn).resolve_left hn15).resolve_left hn24
    exact ns 0 1 2 5 (by decide) (by decide) h01 h12 h25 h05.symm
  have hn15 : ¬ G.Adj (v 1) (v 5) := by
    intro h
    have hn04 : ¬ G.Adj (v 0) (v 4) :=
      fun hh => ns 0 1 5 4 (by decide) (by decide) h01 h h45.symm hh.symm
    have hn24 : ¬ G.Adj (v 2) (v 4) :=
      fun hh => ns 2 1 5 4 (by decide) (by decide) h12.symm h h45.symm hh.symm
    have h03' : G.Adj (v 0) (v 3) := h03.resolve_right (not_or.mpr ⟨hn04,not_or.mpr ⟨hn13,hn⟩⟩)
    have h23 : G.Adj (v 2) (v 3) := ((h13.resolve_left hn13).resolve_left hn).resolve_right hn24
    exact ns 0 1 2 3 (by decide) (by decide) h01 h12 h23 h03'.symm
  have hn04 : ¬ G.Adj (v 0) (v 4) := by
    intro h
    have hn24 : ¬ G.Adj (v 2) (v 4) :=
      fun hh => ns 4 0 1 2 (by decide) (by decide) h.symm h01 h12 hh
    have h23 : G.Adj (v 2) (v 3) := ((h13.resolve_left hn13).resolve_left hn).resolve_right hn24
    have h25 : G.Adj (v 2) (v 5) := ((h14.resolve_left hn).resolve_left hn15).resolve_left hn24
    exact ns 3 4 5 2 (by decide) (by decide) h34 h45 h25.symm h23
  have hn24 : ¬ G.Adj (v 2) (v 4) := by
    intro h
    have h03' : G.Adj (v 0) (v 3) := h03.resolve_right (not_or.mpr ⟨hn04,not_or.mpr ⟨hn13,hn⟩⟩)
    have h05 : G.Adj (v 0) (v 5) := (h04.resolve_left hn04).resolve_right (not_or.mpr ⟨hn,hn15⟩)
    exact ns 3 4 5 0 (by decide) (by decide) h34 h45 h05.symm h03'
  have h03' : G.Adj (v 0) (v 3) := h03.resolve_right (not_or.mpr ⟨hn04,not_or.mpr ⟨hn13,hn⟩⟩)
  have h05 : G.Adj (v 0) (v 5) := (h04.resolve_left hn04).resolve_right (not_or.mpr ⟨hn,hn15⟩)
  have h23 : G.Adj (v 2) (v 3) := ((h13.resolve_left hn13).resolve_left hn).resolve_right hn24
  have h25 : G.Adj (v 2) (v 5) := ((h14.resolve_left hn).resolve_left hn15).resolve_left hn24
  exact ns 0 3 2 5 (by decide) (by decide) h03' h23.symm h25 h05.symm

/-- The centre lemma directly in the edge-set interface used by F09. -/
theorem disjoint_two_paths_centres_of_clique (hg : 5 ≤ G.egirth)
    (v : Fin 6 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4)) (h45 : G.Adj (v 4) (v 5))
    {Q : Finset G.edgeSet} (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (he0 : edge G h01 ∈ Q) (he1 : edge G h12 ∈ Q)
    (he3 : edge G h34 ∈ Q) (he4 : edge G h45 ∈ Q) : G.Adj (v 1) (v 4) := by
  apply disjoint_two_paths_centres hg v hv h01 h12 h34 h45
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he0 he3
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he0 he4
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he1 he3
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he1 he4

/-- A five-edge path cannot be contained in a strong clique. The intervening
edge is part of G, not an assumption about the conflict graph alone. -/
theorem no_five_edge_path_clique (hg : 5 ≤ G.egirth)
    (v : Fin 6 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h23 : G.Adj (v 2) (v 3)) (h34 : G.Adj (v 3) (v 4))
    (h45 : G.Adj (v 4) (v 5))
    {Q : Finset G.edgeSet} (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (he0 : edge G h01 ∈ Q) (he1 : edge G h12 ∈ Q)
    (he3 : edge G h34 ∈ Q) (he4 : edge G h45 ∈ Q) : False := by
  have h14 := disjoint_two_paths_centres_of_clique hg v hv h01 h12 h34 h45 hQ he0 he1 he3 he4
  rcases square_backtrack hg h12 h23 h34 h14.symm with h|h
  · exact (by decide : (1 : Fin 6) ≠ 3) (hv h)
  · exact (by decide : (2 : Fin 6) ≠ 4) (hv h)

/-- F09, endpoint lemma 1.2: a disjoint edge meeting both conflict
neighbourhoods of a two-edge path is of type A or type B. -/
theorem path_edge_attachment (hg : 5 ≤ G.egirth)
    (v : Fin 5 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h0 : Cross (G := G) (v 0) (v 1) (v 3) (v 4))
    (h1 : Cross (G := G) (v 1) (v 2) (v 3) (v 4)) :
    (G.Adj (v 1) (v 3) ∨ G.Adj (v 1) (v 4)) ∨
    ((G.Adj (v 0) (v 3) ∧ G.Adj (v 2) (v 4)) ∨
      (G.Adj (v 0) (v 4) ∧ G.Adj (v 2) (v 3))) := by
  by_cases ha : G.Adj (v 1) (v 3) ∨ G.Adj (v 1) (v 4)
  · exact Or.inl ha
  apply Or.inr
  unfold Cross at h0 h1
  have hn13 := (not_or.mp ha).1
  have hn14 := (not_or.mp ha).2
  have hl : G.Adj (v 0) (v 3) ∨ G.Adj (v 0) (v 4) := by
    rcases h0 with h|h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn13 h).elim
    · exact (hn14 h).elim
  have hr : G.Adj (v 2) (v 3) ∨ G.Adj (v 2) (v 4) :=
    (h1.resolve_left hn13).resolve_left hn14
  rcases hl with hl|hl <;> rcases hr with hr|hr
  · rcases square_backtrack hg h01 h12 hr hl.symm with h|h
    · exact ((by decide : (0 : Fin 5) ≠ 2) (hv h)).elim
    · exact ((by decide : (1 : Fin 5) ≠ 3) (hv h)).elim
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · rcases square_backtrack hg h01 h12 hr hl.symm with h|h
    · exact ((by decide : (0 : Fin 5) ≠ 2) (hv h)).elim
    · exact ((by decide : (1 : Fin 5) ≠ 4) (hv h)).elim

/-- The other path-pair exclusion in F09: vertex-disjoint paths of lengths
three and two cannot have all five edges in a strong clique. -/
theorem no_three_two_paths_clique (hg : 5 ≤ G.egirth)
    (v : Fin 7 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h23 : G.Adj (v 2) (v 3)) (h45 : G.Adj (v 4) (v 5))
    (h56 : G.Adj (v 5) (v 6))
    {Q : Finset G.edgeSet} (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (he0 : edge G h01 ∈ Q) (he1 : edge G h12 ∈ Q) (he2 : edge G h23 ∈ Q)
    (he4 : edge G h45 ∈ Q) (he5 : edge G h56 ∈ Q) : False := by
  have h15 : G.Adj (v 1) (v 5) :=
    disjoint_two_paths_centres_of_clique hg (v ∘ ![0,1,2,4,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,5,6] : Fin 6 → Fin 7)))
      h01 h12 h45 h56 hQ he0 he1 he4 he5
  have h25 : G.Adj (v 2) (v 5) :=
    disjoint_two_paths_centres_of_clique hg (v ∘ ![1,2,3,4,5,6])
      (hv.comp (by decide : Function.Injective (![1,2,3,4,5,6] : Fin 6 → Fin 7)))
      h12 h23 h45 h56 hQ he1 he2 he4 he5
  exact no_triangle hg h12 h25 h15.symm

private theorem no_square_injective {ι : Type*} (hg : 5 ≤ G.egirth)
    (v : ι → V) (hv : Function.Injective v) {a b c d : ι}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj (v a) (v b)) (hbc : G.Adj (v b) (v c))
    (hcd : G.Adj (v c) (v d)) (hda : G.Adj (v d) (v a)) : False := by
  rcases square_backtrack hg hab hbc hcd hda with h|h
  · exact hac (hv h)
  · exact hbd (hv h)

/-- The A attachment is unique: all other path-to-edge connections are
excluded. In particular the A and B alternatives cannot both hold. -/
theorem path_edge_typeA_unique (hg : 5 ≤ G.egirth)
    (v : Fin 5 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4)) (h13 : G.Adj (v 1) (v 3)) :
    ¬ G.Adj (v 0) (v 3) ∧ ¬ G.Adj (v 0) (v 4) ∧
    ¬ G.Adj (v 2) (v 3) ∧ ¬ G.Adj (v 2) (v 4) ∧ ¬ G.Adj (v 1) (v 4) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun h => no_triangle hg h01 h13 h.symm
  · exact fun h => no_square_injective hg v hv (by decide) (by decide) h01 h13 h34 h.symm
  · exact fun h => no_triangle hg h12 h h13.symm
  · exact fun h => no_square_injective hg v hv (by decide) (by decide) h12.symm h13 h34 h.symm
  · exact fun h => no_triangle hg h13 h34 h.symm

/-- The B attachment likewise has no additional path-to-edge connection. -/
theorem path_edge_typeB_unique (hg : 5 ≤ G.egirth) (v : Fin 5 → V)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4))
    (h03 : G.Adj (v 0) (v 3)) (h24 : G.Adj (v 2) (v 4)) :
    ¬ G.Adj (v 1) (v 3) ∧ ¬ G.Adj (v 1) (v 4) ∧
    ¬ G.Adj (v 0) (v 4) ∧ ¬ G.Adj (v 2) (v 3) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact fun h => no_triangle hg h01 h h03.symm
  · exact fun h => no_triangle hg h12 h24 h.symm
  · exact fun h => no_triangle hg h03 h34 h.symm
  · exact fun h => no_triangle hg h24 h34.symm h.symm

/-- Two vertex-disjoint B attachments cannot conflict with each other. -/
theorem two_typeB_not_conflicting (hg : 5 ≤ G.egirth)
    (v : Fin 7 → V) (hv : Function.Injective v)
    (h34 : G.Adj (v 3) (v 4)) (h56 : G.Adj (v 5) (v 6))
    (h03 : G.Adj (v 0) (v 3)) (h24 : G.Adj (v 2) (v 4))
    (h05 : G.Adj (v 0) (v 5)) (h26 : G.Adj (v 2) (v 6)) :
    ¬ Cross (G := G) (v 3) (v 4) (v 5) (v 6) := by
  rintro (h|h|h|h)
  · exact no_triangle hg h03 h h05.symm
  · exact no_square_injective hg v hv (by decide) (by decide) h03 h h56.symm h05.symm
  · exact no_square_injective hg v hv (by decide) (by decide) h24 h h56 h26.symm
  · exact no_triangle hg h24 h h26.symm

/-- Two A attachments can conflict only through their outer endpoints. -/
theorem two_typeA_outer_adj (hg : 5 ≤ G.egirth)
    (v : Fin 7 → V) (hv : Function.Injective v)
    (h34 : G.Adj (v 3) (v 4)) (h56 : G.Adj (v 5) (v 6))
    (h13 : G.Adj (v 1) (v 3)) (h15 : G.Adj (v 1) (v 5))
    (hc : Cross (G := G) (v 3) (v 4) (v 5) (v 6)) : G.Adj (v 4) (v 6) := by
  rcases hc with h|h|h|h
  · exact (no_triangle hg h13 h h15.symm).elim
  · exact (no_square_injective hg v hv (by decide) (by decide) h13 h h56.symm h15.symm).elim
  · exact (no_square_injective hg v hv (by decide) (by decide) h15 h.symm h34.symm h13.symm).elim
  · exact h

/-- Between an A and a B attachment, exactly one endpoint of B can meet
the outer endpoint of A; the inner endpoint of A cannot meet either. -/
theorem typeA_typeB_connection (hg : 5 ≤ G.egirth)
    (v : Fin 7 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h56 : G.Adj (v 5) (v 6)) (h13 : G.Adj (v 1) (v 3))
    (h05 : G.Adj (v 0) (v 5)) (h26 : G.Adj (v 2) (v 6))
    (hc : Cross (G := G) (v 3) (v 4) (v 5) (v 6)) :
    ¬ G.Adj (v 3) (v 5) ∧ ¬ G.Adj (v 3) (v 6) ∧
    (G.Adj (v 4) (v 5) ∨ G.Adj (v 4) (v 6)) ∧
    ¬ (G.Adj (v 4) (v 5) ∧ G.Adj (v 4) (v 6)) := by
  have hn35 : ¬ G.Adj (v 3) (v 5) := fun h =>
    no_square_injective hg v hv (by decide) (by decide) h13 h h05.symm h01
  have hn36 : ¬ G.Adj (v 3) (v 6) := fun h =>
    no_square_injective hg v hv (by decide) (by decide) h13 h h26.symm h12.symm
  refine ⟨hn35,hn36,(hc.resolve_left hn35).resolve_left hn36,?_⟩
  rintro ⟨h45,h46⟩
  exact no_triangle hg h45 h56 h46.symm

/-- The interaction obstruction behind the last forbidden five-edge forest
shape: two A attachments and one B attachment cannot be pairwise conflicting. -/
theorem two_typeA_one_typeB_impossible (hg : 5 ≤ G.egirth)
    (v : Fin 9 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4)) (h56 : G.Adj (v 5) (v 6))
    (h78 : G.Adj (v 7) (v 8))
    (h13 : G.Adj (v 1) (v 3)) (h15 : G.Adj (v 1) (v 5))
    (h07 : G.Adj (v 0) (v 7)) (h28 : G.Adj (v 2) (v 8))
    (hab : Cross (G := G) (v 3) (v 4) (v 5) (v 6))
    (hac : Cross (G := G) (v 3) (v 4) (v 7) (v 8))
    (hbc : Cross (G := G) (v 5) (v 6) (v 7) (v 8)) : False := by
  have h46 : G.Adj (v 4) (v 6) := two_typeA_outer_adj hg
    (v ∘ ![0,1,2,3,4,5,6])
    (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6] : Fin 7 → Fin 9)))
    h34 h56 h13 h15 hab
  have h4 : G.Adj (v 4) (v 7) ∨ G.Adj (v 4) (v 8) :=
    (typeA_typeB_connection hg (v ∘ ![0,1,2,3,4,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,7,8] : Fin 7 → Fin 9)))
      h01 h12 h78 h13 h07 h28 hac).2.2.1
  have h6 : G.Adj (v 6) (v 7) ∨ G.Adj (v 6) (v 8) :=
    (typeA_typeB_connection hg (v ∘ ![0,1,2,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,7,8] : Fin 7 → Fin 9)))
      h01 h12 h78 h15 h07 h28 hbc).2.2.1
  rcases h4 with h4|h4 <;> rcases h6 with h6|h6
  · exact no_triangle hg h46 h6 h4.symm
  · exact no_square_injective hg v hv (by decide) (by decide) h4 h78 h6.symm h46.symm
  · exact no_square_injective hg v hv (by decide) (by decide) h4 h78.symm h6.symm h46.symm
  · exact no_triangle hg h46 h6 h4.symm

/-- Three A attachments would give the path centre five distinct neighbours. -/
theorem three_typeA_impossible [Fintype V] (hΔ : MaxDegreeFour G)
    (v : Fin 9 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h13 : G.Adj (v 1) (v 3)) (h15 : G.Adj (v 1) (v 5))
    (h17 : G.Adj (v 1) (v 7)) : False := by
  let S : Finset (Fin 9) := {0,2,3,5,7}
  have hS : S.card = 5 := by decide
  have hc : (S.image v).card = 5 := (Finset.card_image_of_injective S hv).trans hS
  have hs : S.image v ⊆ G.neighborFinset (v 1) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
    apply (G.mem_neighborFinset _ _).mpr
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h15
    · exact h17
  have hh := Finset.card_le_card hs
  rw [hc, SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hd := hΔ (v 1)
  omega

set_option maxHeartbeats 2000000 in
/-- F09's third excluded forest shape, in its endpoint witness interface.
The 64 orientation cases below use only the proved A/B lemmas. -/
theorem no_path_three_edges_cross [Fintype V] (hΔ : MaxDegreeFour G)
    (hg : 5 ≤ G.egirth) (v : Fin 9 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (he0 : G.Adj (v 3) (v 4)) (he1 : G.Adj (v 5) (v 6))
    (he2 : G.Adj (v 7) (v 8))
    (hc00 : Cross (G := G) (v 0) (v 1) (v 3) (v 4))
    (hc01 : Cross (G := G) (v 1) (v 2) (v 3) (v 4))
    (hc10 : Cross (G := G) (v 0) (v 1) (v 5) (v 6))
    (hc11 : Cross (G := G) (v 1) (v 2) (v 5) (v 6))
    (hc20 : Cross (G := G) (v 0) (v 1) (v 7) (v 8))
    (hc21 : Cross (G := G) (v 1) (v 2) (v 7) (v 8))
    (hp01 : Cross (G := G) (v 3) (v 4) (v 5) (v 6))
    (hp02 : Cross (G := G) (v 3) (v 4) (v 7) (v 8))
    (hp12 : Cross (G := G) (v 5) (v 6) (v 7) (v 8)) : False := by
  have ht0 := path_edge_attachment hg (v ∘ ![0,1,2,3,4])
    (hv.comp (by decide : Function.Injective (![0,1,2,3,4] : Fin 5 → Fin 9))) h01 h12 hc00 hc01
  have ht1 := path_edge_attachment hg (v ∘ ![0,1,2,5,6])
    (hv.comp (by decide : Function.Injective (![0,1,2,5,6] : Fin 5 → Fin 9))) h01 h12 hc10 hc11
  have ht2 := path_edge_attachment hg (v ∘ ![0,1,2,7,8])
    (hv.comp (by decide : Function.Injective (![0,1,2,7,8] : Fin 5 → Fin 9))) h01 h12 hc20 hc21
  rcases ht0 with (h0|h0)|(⟨h0,k0⟩|⟨h0,k0⟩) <;>
    rcases ht1 with (h1|h1)|(⟨h1,k1⟩|⟨h1,k1⟩) <;>
    rcases ht2 with (h2|h2)|(⟨h2,k2⟩|⟨h2,k2⟩)
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,3,4,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6,7,8] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,3,4,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6,8,7] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6,7,8] : Fin 9 → Fin 9)))
      h01 h12 he0 he1 he2 h0 h1 h2 k2
      hp01 hp02 hp12
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6,8,7] : Fin 9 → Fin 9)))
      h01 h12 he0 he1 he2.symm h0 h1 h2 k2
      hp01 hp02.flipRight hp12.flipRight
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,3,4,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5,7,8] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,3,4,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5,8,7] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5,7,8] : Fin 9 → Fin 9)))
      h01 h12 he0 he1.symm he2 h0 h1 h2 k2
      hp01.flipRight hp02 hp12.flipLeft
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5,8,7] : Fin 9 → Fin 9)))
      h01 h12 he0 he1.symm he2.symm h0 h1 h2 k2
      hp01.flipRight hp02.flipRight hp12.flipLeft.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,7,8,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,7,8,5,6] : Fin 9 → Fin 9)))
      h01 h12 he0 he2 he1 h0 h2 h1 k1
      hp02 hp01 hp12.symm
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,8,7,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,8,7,5,6] : Fin 9 → Fin 9)))
      h01 h12 he0 he2.symm he1 h0 h2 h1 k1
      hp02.flipRight hp01 hp12.symm.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,7,8] : Fin 7 → Fin 9)))
      he1 he2 h1 k1 h2 k2 hp12
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,8,7] : Fin 7 → Fin 9)))
      he1 he2.symm h1 k1 h2 k2 hp12.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,7,8,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,7,8,6,5] : Fin 9 → Fin 9)))
      h01 h12 he0 he2 he1.symm h0 h2 h1 k1
      hp02 hp01.flipRight hp12.symm.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,3,4,8,7,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,8,7,6,5] : Fin 9 → Fin 9)))
      h01 h12 he0 he2.symm he1.symm h0 h2 h1 k1
      hp02.flipRight hp01.flipRight hp12.symm.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,7,8] : Fin 7 → Fin 9)))
      he1.symm he2 h1 k1 h2 k2 hp12.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,8,7] : Fin 7 → Fin 9)))
      he1.symm he2.symm h1 k1 h2 k2 hp12.flipLeft.flipRight
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,4,3,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6,7,8] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,4,3,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6,8,7] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6,7,8] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he1 he2 h0 h1 h2 k2
      hp01.flipLeft hp02.flipLeft hp12
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6,8,7] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he1 he2.symm h0 h1 h2 k2
      hp01.flipLeft hp02.flipLeft.flipRight hp12.flipRight
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,4,3,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5,7,8] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact three_typeA_impossible hΔ (v ∘ ![0,1,2,4,3,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5,8,7] : Fin 9 → Fin 9)))
      h01 h12 h0 h1 h2
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5,7,8] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he1.symm he2 h0 h1 h2 k2
      hp01.flipLeft.flipRight hp02.flipLeft hp12.flipLeft
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5,8,7] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he1.symm he2.symm h0 h1 h2 k2
      hp01.flipLeft.flipRight hp02.flipLeft.flipRight hp12.flipLeft.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,7,8,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,7,8,5,6] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he2 he1 h0 h2 h1 k1
      hp02.flipLeft hp01.flipLeft hp12.symm
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,8,7,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,8,7,5,6] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he2.symm he1 h0 h2 h1 k1
      hp02.flipLeft.flipRight hp01.flipLeft hp12.symm.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,5,6,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,7,8] : Fin 7 → Fin 9)))
      he1 he2 h1 k1 h2 k2 hp12
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,5,6,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,8,7] : Fin 7 → Fin 9)))
      he1 he2.symm h1 k1 h2 k2 hp12.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,7,8,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,7,8,6,5] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he2 he1.symm h0 h2 h1 k1
      hp02.flipLeft hp01.flipLeft.flipRight hp12.symm.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,4,3,8,7,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,8,7,6,5] : Fin 9 → Fin 9)))
      h01 h12 he0.symm he2.symm he1.symm h0 h2 h1 k1
      hp02.flipLeft.flipRight hp01.flipLeft.flipRight hp12.symm.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,6,5,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,7,8] : Fin 7 → Fin 9)))
      he1.symm he2 h1 k1 h2 k2 hp12.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,6,5,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,8,7] : Fin 7 → Fin 9)))
      he1.symm he2.symm h1 k1 h2 k2 hp12.flipLeft.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,5,6,7,8,3,4])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,7,8,3,4] : Fin 9 → Fin 9)))
      h01 h12 he1 he2 he0 h1 h2 h0 k0
      hp12 hp01.symm hp02.symm
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,5,6,8,7,3,4])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,8,7,3,4] : Fin 9 → Fin 9)))
      h01 h12 he1 he2.symm he0 h1 h2 h0 k0
      hp12.flipRight hp01.symm hp02.symm.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,7,8] : Fin 7 → Fin 9)))
      he0 he2 h0 k0 h2 k2 hp02
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,8,7] : Fin 7 → Fin 9)))
      he0 he2.symm h0 k0 h2 k2 hp02.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,6,5,7,8,3,4])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,7,8,3,4] : Fin 9 → Fin 9)))
      h01 h12 he1.symm he2 he0 h1 h2 h0 k0
      hp12.flipLeft hp01.symm.flipLeft hp02.symm
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,6,5,8,7,3,4])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,8,7,3,4] : Fin 9 → Fin 9)))
      h01 h12 he1.symm he2.symm he0 h1 h2 h0 k0
      hp12.flipLeft.flipRight hp01.symm.flipLeft hp02.symm.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,7,8] : Fin 7 → Fin 9)))
      he0 he2 h0 k0 h2 k2 hp02
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,8,7] : Fin 7 → Fin 9)))
      he0 he2.symm h0 k0 h2 k2 hp02.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6] : Fin 7 → Fin 9)))
      he0 he1 h0 k0 h1 k1 hp01
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6] : Fin 7 → Fin 9)))
      he0 he1 h0 k0 h1 k1 hp01
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6] : Fin 7 → Fin 9)))
      he0 he1 h0 k0 h1 k1 hp01
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,5,6] : Fin 7 → Fin 9)))
      he0 he1 h0 k0 h1 k1 hp01
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5] : Fin 7 → Fin 9)))
      he0 he1.symm h0 k0 h1 k1 hp01.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5] : Fin 7 → Fin 9)))
      he0 he1.symm h0 k0 h1 k1 hp01.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5] : Fin 7 → Fin 9)))
      he0 he1.symm h0 k0 h1 k1 hp01.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,3,4,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,3,4,6,5] : Fin 7 → Fin 9)))
      he0 he1.symm h0 k0 h1 k1 hp01.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,5,6,7,8,4,3])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,7,8,4,3] : Fin 9 → Fin 9)))
      h01 h12 he1 he2 he0.symm h1 h2 h0 k0
      hp12 hp01.symm.flipRight hp02.symm.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,5,6,8,7,4,3])
      (hv.comp (by decide : Function.Injective (![0,1,2,5,6,8,7,4,3] : Fin 9 → Fin 9)))
      h01 h12 he1 he2.symm he0.symm h1 h2 h0 k0
      hp12.flipRight hp01.symm.flipRight hp02.symm.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,7,8] : Fin 7 → Fin 9)))
      he0.symm he2 h0 k0 h2 k2 hp02.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,8,7] : Fin 7 → Fin 9)))
      he0.symm he2.symm h0 k0 h2 k2 hp02.flipLeft.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,6,5,7,8,4,3])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,7,8,4,3] : Fin 9 → Fin 9)))
      h01 h12 he1.symm he2 he0.symm h1 h2 h0 k0
      hp12.flipLeft hp01.symm.flipLeft.flipRight hp02.symm.flipRight
  · exact two_typeA_one_typeB_impossible hg (v ∘ ![0,1,2,6,5,8,7,4,3])
      (hv.comp (by decide : Function.Injective (![0,1,2,6,5,8,7,4,3] : Fin 9 → Fin 9)))
      h01 h12 he1.symm he2.symm he0.symm h1 h2 h0 k0
      hp12.flipLeft.flipRight hp01.symm.flipLeft.flipRight hp02.symm.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,7,8])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,7,8] : Fin 7 → Fin 9)))
      he0.symm he2 h0 k0 h2 k2 hp02.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,8,7])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,8,7] : Fin 7 → Fin 9)))
      he0.symm he2.symm h0 k0 h2 k2 hp02.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6] : Fin 7 → Fin 9)))
      he0.symm he1 h0 k0 h1 k1 hp01.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6] : Fin 7 → Fin 9)))
      he0.symm he1 h0 k0 h1 k1 hp01.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6] : Fin 7 → Fin 9)))
      he0.symm he1 h0 k0 h1 k1 hp01.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,5,6])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,5,6] : Fin 7 → Fin 9)))
      he0.symm he1 h0 k0 h1 k1 hp01.flipLeft
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5] : Fin 7 → Fin 9)))
      he0.symm he1.symm h0 k0 h1 k1 hp01.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5] : Fin 7 → Fin 9)))
      he0.symm he1.symm h0 k0 h1 k1 hp01.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5] : Fin 7 → Fin 9)))
      he0.symm he1.symm h0 k0 h1 k1 hp01.flipLeft.flipRight
  · exact two_typeB_not_conflicting hg (v ∘ ![0,1,2,4,3,6,5])
      (hv.comp (by decide : Function.Injective (![0,1,2,4,3,6,5] : Fin 7 → Fin 9)))
      he0.symm he1.symm h0 k0 h1 k1 hp01.flipLeft.flipRight

/-- A two-edge path and three vertex-disjoint single edges cannot be
contained in a strong clique in an ambient graph of maximum degree four
and girth at least five. -/
theorem no_path_three_edges_clique [Fintype V] (hΔ : MaxDegreeFour G)
    (hg : 5 ≤ G.egirth) (v : Fin 9 → V) (hv : Function.Injective v)
    (h01 : G.Adj (v 0) (v 1)) (h12 : G.Adj (v 1) (v 2))
    (h34 : G.Adj (v 3) (v 4)) (h56 : G.Adj (v 5) (v 6))
    (h78 : G.Adj (v 7) (v 8))
    {Q : Finset G.edgeSet} (hQ : (L2 G).IsClique (Q : Set G.edgeSet))
    (he0 : edge G h01 ∈ Q) (he1 : edge G h12 ∈ Q)
    (he2 : edge G h34 ∈ Q) (he3 : edge G h56 ∈ Q)
    (he4 : edge G h78 ∈ Q) : False := by
  apply no_path_three_edges_cross hΔ hg v hv h01 h12 h34 h56 h78
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he0 he2
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he1 he2
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he0 he3
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he1 he3
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he0 he4
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he1 he4
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he2 he3
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he2 he4
  · exact cross_of_clique _ _ rfl rfl (hv.ne (by decide)) (hv.ne (by decide))
      (hv.ne (by decide)) (hv.ne (by decide)) hQ he3 he4

end GirthFive

/-- Ambient common extensions, restricted to the selected edge set F. -/
def commonExtensions {V : Type*} (G : SimpleGraph V) (F Q : Finset G.edgeSet) :
    Finset G.edgeSet := (F \ Q).filter (fun e => ∀ q ∈ Q, (L2 G).Adj e q)

@[simp] theorem mem_commonExtensions {V : Type*} (G : SimpleGraph V)
    (F Q : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ commonExtensions G F Q ↔
      e ∈ F ∧ e ∉ Q ∧ ∀ q ∈ Q, (L2 G).Adj e q := by
  simp [commonExtensions, and_assoc]

/-- F09, the full independence assertion for common extensions of any
four-edge strong clique. No shape classification is needed for this part. -/
theorem commonExtensions_independent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) (hg : 5 ≤ G.egirth)
    (F Q : Finset G.edgeSet) (hdeg : DegreeTwoEdgeSet G F)
    (hQF : Q ⊆ F) (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) (hcard : Q.card = 4) :
    Independent (L2 G) (commonExtensions G F Q) := by
  intro e he f hf hef
  obtain ⟨heF,heQ,hec⟩ := (mem_commonExtensions G F Q e).mp he
  obtain ⟨hfF,hfQ,hfc⟩ := (mem_commonExtensions G F Q f).mp hf
  let T := insert e (insert f Q)
  have hTF : T ⊆ F := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact heF
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hfF
    exact hQF hx
  have hTd : DegreeTwoEdgeSet G T := by
    intro v
    apply (Finset.card_le_card (Finset.filter_subset_filter _ hTF)).trans (hdeg v)
  have hT : (L2 G).IsClique (T : Set G.edgeSet) := by
    intro x hx y hy hxy
    change x ∈ T at hx
    change y ∈ T at hy
    simp only [T, Finset.mem_insert] at hx hy
    rcases hx with rfl|rfl|hxQ <;> rcases hy with rfl|rfl|hyQ
    · exact (hxy rfl).elim
    · exact hef
    · exact hec y hyQ
    · exact hef.symm
    · exact (hxy rfl).elim
    · exact hfc y hyQ
    · exact (hec x hxQ).symm
    · exact (hfc x hxQ).symm
    · exact hQ hxQ hyQ hxy
  have hc := GirthClique.girth_degreeTwo_clique_five G hΔ hg T hTd hT
  have hn : e ∉ insert f Q := by simp [hef.ne,heQ]
  have hct : T.card = 6 := by
    simp only [T, Finset.card_insert_of_notMem hn, Finset.card_insert_of_notMem hfQ, hcard]
  omega

end Se20Part
