import Se20Part.External
import Mathlib.Order.PiLex
import Mathlib.Data.Set.Finite.Lemmas

noncomputable section
open scoped Classical BigOperators
open Finset
namespace Se20Part
namespace HaxellProof
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {V I : Type} [Fintype V] [Fintype I]
variable (G : SimpleGraph V) (part : V → I)

def Partial (S : Finset V) : Prop :=
  Set.InjOn part (S : Set V) ∧ ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

def blockers (S : Finset V) (x : V) : Finset V := S.filter (G.Adj x)

@[simp] theorem mem_blockers (S : Finset V) (x y : V) :
    y ∈ blockers G S x ↔ y ∈ S ∧ G.Adj x y := by simp [blockers]

theorem blockers_subset (S : Finset V) (x : V) : blockers G S x ⊆ S := filter_subset _ _

theorem Partial.empty : Partial G part ∅ := by simp [Partial,Set.InjOn]

theorem Partial.insert_vertex {S : Finset V} (hS : Partial G part S) {v : V}
    (hp : part v ∉ S.image part) (ha : ∀ y ∈ S, ¬ G.Adj v y) :
    Partial G part (insert v S) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.mem_coe,mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact (hp (mem_image.mpr ⟨y,hy,hxy.symm⟩)).elim
    · exact (hp (mem_image.mpr ⟨x,hx,hxy⟩)).elim
    · exact hS.1 hx hy hxy
  · intro x hx y hy hxy
    simp only [mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact G.irrefl hxy
    · exact ha y hy hxy
    · exact ha x hx hxy.symm
    · exact hS.2 x hx y hy hxy

theorem Partial.swap {S : Finset V} (hS : Partial G part S) {v y : V}
    (hy : y ∈ S) (hp : part v = part y) (ha : ∀ z ∈ S, ¬ G.Adj v z) :
    Partial G part (insert v (S.erase y)) := by
  apply Partial.insert_vertex
  · exact ⟨hS.1.mono (by intro z hz; exact mem_of_mem_erase hz),
      fun x hx z hz => hS.2 x (mem_of_mem_erase hx) z (mem_of_mem_erase hz)⟩
  · rintro h
    obtain ⟨z,hz,hzv⟩ := mem_image.mp h
    exact (mem_erase.mp hz).1 (hS.1 (mem_of_mem_erase hz) hy (hzv.trans hp))
  · intro z hz
    exact ha z (mem_of_mem_erase hz)

theorem swap_image {S : Finset V} {v y : V} (hy : y ∈ S) (hp : part v = part y) :
    (insert v (S.erase y)).image part = S.image part := by
  ext i
  simp only [image_insert,mem_insert,mem_image,mem_erase]
  constructor
  · rintro (rfl | ⟨z,⟨hzy,hz⟩,rfl⟩)
    · exact ⟨y,hy,hp.symm⟩
    · exact ⟨z,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    by_cases hzy : z = y
    · left; simpa [hzy] using hp.symm
    · exact Or.inr ⟨z,⟨hzy,hz⟩,rfl⟩

/-- A bounded augmenting sequence. Earlier vertices and their blockers must
be nonadjacent to the next vertex. Only the last blocker set may be empty. -/
structure Config where
  S : Finset V
  count : Fin (Fintype.card V + 1)
  vertex : Fin (Fintype.card V) → V
  deriving Fintype

def active (c : Config (V := V)) : Finset (Fin (Fintype.card V)) :=
  univ.filter (fun j => j.val < c.count.val)

@[simp] theorem mem_active (c : Config (V := V)) (j : Fin (Fintype.card V)) :
    j ∈ active c ↔ j.val < c.count.val := by simp [active]

def Valid (c : Config (V := V)) : Prop :=
  Partial G part c.S ∧
  (∀ j ∈ active c,
    part (c.vertex j) ∉ c.S.image part ∨
      ∃ k : Fin (Fintype.card V), k < j ∧
        ∃ y ∈ blockers G c.S (c.vertex k), part y = part (c.vertex j)) ∧
  (∀ j ∈ active c, ∀ k : Fin (Fintype.card V), k < j →
    ¬ G.Adj (c.vertex j) (c.vertex k) ∧
      ∀ y ∈ blockers G c.S (c.vertex k), ¬ G.Adj (c.vertex j) y) ∧
  (∀ j : Fin (Fintype.card V), j.val+1 < c.count.val →
    (blockers G c.S (c.vertex j)).Nonempty)

theorem active_card (c : Config (V := V)) : (active c).card = c.count.val := by
  have h := c.count.isLt
  let f : Fin c.count.val → Fin (Fintype.card V) := fun j => ⟨j.val,by omega⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun j : Fin (Fintype.card V) => j.val) hab
  have he : Finset.univ.image f = active c := by
    ext j
    simp only [mem_image,mem_univ,true_and,mem_active]
    constructor
    · rintro ⟨k,rfl⟩; exact k.isLt
    · intro hj; exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩
  rw [← he,card_image_of_injective _ hi,card_univ,Fintype.card_fin]

def blocked (c : Config (V := V)) : Finset V :=
  (active c).biUnion (fun j => blockers G c.S (c.vertex j))

theorem blocked_subset (c : Config (V := V)) : blocked G c ⊆ c.S := by
  intro y hy
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp hy
  exact (mem_blockers G _ _ _).mp hj |>.1

theorem Valid.disjoint_blockers {c : Config (V := V)} (hc : Valid G part c) :
    (active c : Set (Fin (Fintype.card V))).Pairwise
      (fun j k => Disjoint (blockers G c.S (c.vertex j)) (blockers G c.S (c.vertex k))) := by
  intro j hj k hk hne
  apply disjoint_left.mpr
  intro y hyj hyk
  rcases lt_or_gt_of_ne hne with h | h
  · exact (hc.2.2.1 k hk j h).2 y hyj ((mem_blockers G _ _ _).mp hyk).2
  · exact (hc.2.2.1 j hj k h).2 y hyk ((mem_blockers G _ _ _).mp hyj).2

theorem Valid.blocked_card {c : Config (V := V)} (hc : Valid G part c) :
    (blocked G c).card = ∑ j ∈ active c, (blockers G c.S (c.vertex j)).card := by
  exact card_biUnion (hc.disjoint_blockers)

theorem Valid.count_le_blocked {c : Config (V := V)} (hc : Valid G part c)
    (hp : ∀ j ∈ active c, (blockers G c.S (c.vertex j)).Nonempty) :
    c.count.val ≤ (blocked G c).card := by
  rw [hc.blocked_card,← active_card c]
  calc
    _ = ∑ _j ∈ active c, 1 := by simp
    _ ≤ _ := sum_le_sum (fun j hj => (card_pos.mpr (hp j hj)))

/-- Uncovered parts and the parts of the blockers are the available parts. -/
def available (c : Config (V := V)) : Finset I :=
  (univ \ c.S.image part) ∪ (blocked G c).image part

theorem available_card (c : Config (V := V)) (hc : Partial G part c.S) :
    (available G part c).card = Fintype.card I - c.S.card + (blocked G c).card := by
  have hi := hc.1
  have hb := hi.mono (show (blocked G c : Set V) ⊆ c.S from blocked_subset G c)
  have hd : Disjoint (univ \ c.S.image part) ((blocked G c).image part) := by
    apply disjoint_left.mpr
    intro i hi' hb'
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb'
    exact (mem_sdiff.mp hi').2 (mem_image.mpr ⟨y,blocked_subset G c hy,rfl⟩)
  rw [available,card_union_of_disjoint hd,card_sdiff_of_subset (subset_univ _),card_univ,
    card_image_of_injOn hi,card_image_of_injOn hb]

theorem available_nonempty_gain {c : Config (V := V)} (hc : Partial G part c.S)
    (hmiss : ∃ i, i ∉ c.S.image part) :
    (blocked G c).card < (available G part c).card := by
  rw [available_card G part c hc]
  have hlt : (c.S.image part).card < Fintype.card I := by
    obtain ⟨i,hi⟩ := hmiss
    have hproper : c.S.image part ⊂ univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨subset_univ _,by intro h; apply hi; rw [h]; exact mem_univ _⟩
    have := card_lt_card hproper
    simpa using this
  rw [card_image_of_injOn hc.1] at hlt
  omega

def region (J : Finset I) : Finset V := univ.filter (fun v => part v ∈ J)

theorem region_card (J : Finset I) :
    (region part J).card = ∑ i ∈ J, Fintype.card {v // part v = i} := by
  classical
  have he : region part J = J.biUnion (fun i => univ.filter (fun v => part v = i)) := by
    ext v
    simp [region]
  rw [he,card_biUnion]
  · apply sum_congr rfl
    intro i _
    simp only [← Fintype.card_subtype]
  · intro i hi j hj hij
    apply disjoint_left.mpr
    intro v hv hv'
    simp only [mem_filter,mem_univ,true_and] at hv hv'
    exact hij (hv.symm.trans hv')

def neighborhood (T : Finset V) : Finset V := T.biUnion (fun v => G.neighborFinset v)

theorem neighborhood_card (Δ : ℕ) (hd : DegreeLE G Δ) (T : Finset V) :
    (neighborhood G T).card ≤ T.card * Δ := by
  calc
    _ ≤ ∑ v ∈ T, (G.neighborFinset v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ T, Δ := by
      apply sum_le_sum
      intro v _
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using (degreeLE_iff G Δ).mp hd v
    _ = _ := by simp

theorem incomplete_card_lt (S : Finset V) (hsurj : Function.Surjective part)
    (hmiss : ∃ i, i ∉ S.image part) : S.card < Fintype.card V := by
  obtain ⟨i,hi⟩ := hmiss
  obtain ⟨v,hv⟩ := hsurj i
  have hvs : v ∉ S := by intro h; exact hi (mem_image.mpr ⟨v,h,hv⟩)
  have hproper : S ⊂ univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨subset_univ _,by intro h; simpa [h] using hvs⟩
  simpa using card_lt_card hproper

/-- The counting step: the available parts cannot be dominated by the sequence
and its blockers. This includes the zero-degree case via surjectivity. -/
theorem extend_vertex (Δ : ℕ) (hd : DegreeLE G Δ)
    (hsurj : Function.Surjective part)
    (hsize : ∀ i, 2 * Δ ≤ Fintype.card {v // part v = i})
    {c : Config (V := V)} (hc : Valid G part c)
    (hmiss : ∃ i, i ∉ c.S.image part)
    (hp : ∀ j ∈ active c, (blockers G c.S (c.vertex j)).Nonempty) :
    ∃ v, part v ∈ available G part c ∧
      (∀ j ∈ active c, ¬ G.Adj v (c.vertex j)) ∧
      ∀ y ∈ blocked G c, ¬ G.Adj v y := by
  let T := (active c).image c.vertex ∪ blocked G c
  have hcT : T.card ≤ 2 * (blocked G c).card := by
    have h1 := card_union_le ((active c).image c.vertex) (blocked G c)
    have h2 := card_image_le (f := c.vertex) (s := active c)
    have h3 := Valid.count_le_blocked G part hc hp
    rw [active_card] at h2
    dsimp only [T]
    omega
  have hgain := available_nonempty_gain G part hc.1 hmiss
  have hregion : 2 * Δ * (available G part c).card ≤ (region part (available G part c)).card := by
    rw [region_card]
    calc
      _ = ∑ _i ∈ available G part c, 2*Δ := by simp; ring
      _ ≤ _ := sum_le_sum (fun i _ => hsize i)
  have hregionpos : 0 < (region part (available G part c)).card := by
    obtain ⟨i,hi⟩ := hmiss
    obtain ⟨v,hv⟩ := hsurj i
    apply card_pos.mpr
    refine ⟨v,?_⟩
    simp only [region,mem_filter,mem_univ,true_and,hv]
    exact mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _,hi⟩)
  have hlt : (neighborhood G T).card < (region part (available G part c)).card := by
    have hneigh := neighborhood_card G Δ hd T
    by_cases hΔ : Δ = 0
    · simp only [hΔ,mul_zero] at hneigh
      omega
    · have hmul := Nat.mul_lt_mul_of_pos_right hgain (by omega : 0 < 2*Δ)
      have hT := Nat.mul_le_mul_right Δ hcT
      nlinarith
  have hnsub : ¬ region part (available G part c) ⊆ neighborhood G T := by
    intro h; have := card_le_card h; omega
  obtain ⟨v,hv,hvn⟩ := not_subset.mp hnsub
  have havoid : ∀ y ∈ T, ¬ G.Adj v y := by
    intro y hy hadj
    apply hvn
    exact mem_biUnion.mpr ⟨y,hy,(G.mem_neighborFinset y v).mpr hadj.symm⟩
  refine ⟨v,(mem_filter.mp hv).2,?_,?_⟩
  · intro j hj
    exact havoid _ (mem_union_left _ (mem_image.mpr ⟨j,hj,rfl⟩))
  · intro y hy
    exact havoid y (mem_union_right _ hy)

def score (c : Config (V := V)) : Lex (Fin (Fintype.card V+1) → ℕ) :=
  toLex (Fin.cons (Fintype.card V-c.S.card) (fun j =>
    if j ∈ active c then (blockers G c.S (c.vertex j)).card else Fintype.card V+1))

theorem score_card {c d : Config (V := V)} (h : c.S.card < d.S.card) :
    score G d < score G c := by
  change Pi.Lex (· < ·) (· < ·) _ _
  refine ⟨0,fun j hj => (Fin.not_lt_zero j hj).elim,?_⟩
  simp only [score,Pi.toLex_apply,Fin.cons_zero]
  have := card_le_univ d.S
  omega

theorem score_degree {c d : Config (V := V)} (hcard : d.S.card = c.S.card)
    (j : Fin (Fintype.card V))
    (heq : ∀ k < j,
      (if k ∈ active d then (blockers G d.S (d.vertex k)).card else Fintype.card V+1) =
      (if k ∈ active c then (blockers G c.S (c.vertex k)).card else Fintype.card V+1))
    (hlt : (if j ∈ active d then (blockers G d.S (d.vertex j)).card else Fintype.card V+1) <
      (if j ∈ active c then (blockers G c.S (c.vertex j)).card else Fintype.card V+1)) :
    score G d < score G c := by
  change Pi.Lex (· < ·) (· < ·) _ _
  refine ⟨j.succ,?_,?_⟩
  · intro k hk
    refine Fin.cases ?_ (fun l hl => ?_) k hk
    · intro _; simp [score,hcard]
    · simpa [score] using heq l (by simpa using hl)
  · simpa [score] using hlt

def appendConfig (c : Config (V := V)) (h : c.count.val < Fintype.card V) (v : V) :
    Config (V := V) :=
  ⟨c.S,⟨c.count.val+1,by omega⟩,Function.update c.vertex ⟨c.count.val,h⟩ v⟩

theorem append_vertex_before (c : Config (V := V)) (h : c.count.val < Fintype.card V)
    (v : V) (j : Fin (Fintype.card V)) (hj : j.val < c.count.val) :
    (appendConfig c h v).vertex j = c.vertex j := by
  simp only [appendConfig,Function.update_apply]
  split_ifs with heq
  · have := congrArg Fin.val heq; dsimp at this; omega
  · rfl

theorem append_valid {c : Config (V := V)} (hc : Valid G part c)
    (h : c.count.val < Fintype.card V) (v : V)
    (hav : part v ∈ available G part c)
    (ha : ∀ j ∈ active c, ¬ G.Adj v (c.vertex j))
    (hb : ∀ y ∈ blocked G c, ¬ G.Adj v y)
    (hp : ∀ j ∈ active c, (blockers G c.S (c.vertex j)).Nonempty) :
    Valid G part (appendConfig c h v) := by
  let d := appendConfig c h v
  have hdS : d.S = c.S := rfl
  have hdcount : d.count.val = c.count.val+1 := rfl
  have hbefore (j : Fin (Fintype.card V)) (hj : j.val < c.count.val) :
      d.vertex j = c.vertex j := append_vertex_before c h v j hj
  have hlast (j : Fin (Fintype.card V)) (hj : j.val = c.count.val) : d.vertex j = v := by
    have heq : j = ⟨c.count.val,h⟩ := Fin.ext hj
    simp [d,appendConfig,heq]
  refine ⟨hc.1,?_,?_,?_⟩
  · intro j hj
    have hj' : j.val < c.count.val+1 := (mem_active _ _).mp hj
    by_cases hprev : j.val < c.count.val
    · rw [hbefore j hprev,hdS]
      rcases hc.2.1 j (by simpa using hprev) with hv | ⟨k,hk,y,hy,hyp⟩
      · exact Or.inl hv
      · refine Or.inr ⟨k,hk,y,?_,hyp⟩
        rw [hbefore k (by have := hk; change k.val < j.val at this; omega)]
        exact hy
    · rw [hlast j (by omega),hdS]
      rcases mem_union.mp hav with hav | hav
      · exact Or.inl (mem_sdiff.mp hav).2
      · obtain ⟨y,hy,hyp⟩ := mem_image.mp hav
        obtain ⟨k,hk,hyk⟩ := mem_biUnion.mp hy
        have hk' := (mem_active _ _).mp hk
        refine Or.inr ⟨k,by change k.val < j.val; omega,y,?_,hyp⟩
        rw [hbefore k hk']
        exact hyk
  · intro j hj k hk
    have hj' : j.val < c.count.val+1 := (mem_active _ _).mp hj
    have hk' : k.val < j.val := hk
    have hkb : k.val < c.count.val := by omega
    rw [hbefore k hkb,hdS]
    by_cases hprev : j.val < c.count.val
    · rw [hbefore j hprev]
      exact hc.2.2.1 j (by simpa using hprev) k hk
    · rw [hlast j (by omega)]
      refine ⟨ha k (by simpa using hkb),?_⟩
      intro y hy
      exact hb y (mem_biUnion.mpr ⟨k,by simpa using hkb,hy⟩)
  · intro j hj
    have hprev : j.val < c.count.val := by change j.val+1 < c.count.val+1 at hj; omega
    rw [hdS,hbefore j hprev]
    exact hp j (by simpa using hprev)

theorem append_score (c : Config (V := V)) (h : c.count.val < Fintype.card V) (v : V) :
    score G (appendConfig c h v) < score G c := by
  let j : Fin (Fintype.card V) := ⟨c.count.val,h⟩
  apply score_degree G (c := c) (d := appendConfig c h v) rfl j
  · intro k hk
    have hprev : k.val < c.count.val := hk
    have hcactive : k ∈ active c := by simpa using hprev
    have hdactive : k ∈ active (appendConfig c h v) := by
      simp only [mem_active,appendConfig]; omega
    rw [if_pos hdactive,if_pos hcactive,append_vertex_before c h v k hprev]
    rfl
  · have hcnot : j ∉ active c := by simp [j]
    have hdyes : j ∈ active (appendConfig c h v) := by simp [j,appendConfig]
    simp only [hcnot,hdyes,if_false,if_true]
    have hh := card_le_univ (blockers G (appendConfig c h v).S ((appendConfig c h v).vertex j))
    omega

theorem swap_blockers (S : Finset V) (v y x : V) (ha : ¬ G.Adj x v) :
    blockers G (insert v (S.erase y)) x = (blockers G S x).erase y := by
  ext z
  simp only [mem_blockers,mem_insert,mem_erase]
  constructor
  · rintro ⟨(rfl | ⟨hzy,hz⟩),hxz⟩
    · exact (ha hxz).elim
    · exact ⟨hzy,hz,hxz⟩
  · rintro ⟨hzy,hz,hxz⟩
    exact ⟨Or.inr ⟨hzy,hz⟩,hxz⟩

theorem swap_improves {c : Config (V := V)} (hc : Valid G part c)
    (j : Fin (Fintype.card V)) (hj : j ∈ active c) (v y : V)
    (hy : y ∈ blockers G c.S (c.vertex j)) (hp : part v = part y)
    (hfree : ∀ z ∈ c.S, ¬ G.Adj v z)
    (hprior : ∀ k : Fin (Fintype.card V), k ≤ j → ¬ G.Adj v (c.vertex k)) :
    ∃ d : Config (V := V), Valid G part d ∧ score G d < score G c := by
  let S' := insert v (c.S.erase y)
  let d : Config (V := V) := ⟨S',⟨j.val+1,by have := j.isLt; omega⟩,c.vertex⟩
  have hyS : y ∈ c.S := (mem_blockers G _ _ _).mp hy |>.1
  have hvS : v ∉ c.S := by
    intro hv
    have hveq := hc.1.1 hv hyS hp
    have hadj := (mem_blockers G _ _ _).mp hy |>.2
    exact hprior j le_rfl (by simpa [hveq] using hadj.symm)
  have hS' : Partial G part S' := Partial.swap G part hc.1 hyS hp hfree
  have himage : S'.image part = c.S.image part := swap_image part hyS hp
  have hcard : S'.card = c.S.card := by
    rw [card_insert_of_notMem (fun h => hvS (mem_of_mem_erase h)),card_erase_of_mem hyS]
    have := card_pos.mpr ⟨y,hyS⟩
    omega
  have hb (k : Fin (Fintype.card V)) (hk : k ≤ j) :
      blockers G S' (c.vertex k) = (blockers G c.S (c.vertex k)).erase y :=
    swap_blockers G c.S v y (c.vertex k) (fun h => hprior k hk h.symm)
  have hbeq (k : Fin (Fintype.card V)) (hk : k < j) :
      blockers G S' (c.vertex k) = blockers G c.S (c.vertex k) := by
    rw [hb k hk.le,erase_eq_of_notMem]
    intro hyk
    have hka : k ∈ active c := by have := (mem_active _ _).mp hj; simp only [mem_active]; exact lt_trans hk this
    exact (disjoint_left.mp (Valid.disjoint_blockers G part hc hka hj hk.ne)) hyk hy
  have hd : Valid G part d := by
    refine ⟨hS',?_,?_,?_⟩
    · intro l hl
      have hlj : l ≤ j := by have := (mem_active _ _).mp hl; change l.val < j.val+1 at this; omega
      have hla : l ∈ active c := by
        have hja := (mem_active _ _).mp hj
        simp only [mem_active]
        exact lt_of_le_of_lt hlj hja
      change part (c.vertex l) ∉ S'.image part ∨ _
      rw [himage]
      rcases hc.2.1 l hla with h | ⟨k,hkl,z,hz,hzp⟩
      · exact Or.inl h
      · refine Or.inr ⟨k,hkl,z,?_,hzp⟩
        change z ∈ blockers G S' (c.vertex k)
        rw [hbeq k (lt_of_lt_of_le hkl hlj)]
        exact hz
    · intro l hl k hkl
      have hlj : l ≤ j := by have := (mem_active _ _).mp hl; change l.val < j.val+1 at this; omega
      have hla : l ∈ active c := by
        have hja := (mem_active _ _).mp hj
        simp only [mem_active]
        exact lt_of_le_of_lt hlj hja
      change ¬ G.Adj (c.vertex l) (c.vertex k) ∧ _
      refine ⟨(hc.2.2.1 l hla k hkl).1,?_⟩
      change ∀ z ∈ blockers G S' (c.vertex k), ¬ G.Adj (c.vertex l) z
      rw [hbeq k (lt_of_lt_of_le hkl hlj)]
      exact (hc.2.2.1 l hla k hkl).2
    · intro k hk
      have hkj : k < j := by change k.val+1 < j.val+1 at hk; omega
      change (blockers G S' (c.vertex k)).Nonempty
      rw [hbeq k hkj]
      apply hc.2.2.2 k
      have := (mem_active _ _).mp hj
      change k.val < j.val at hkj
      omega
  refine ⟨d,hd,?_⟩
  apply score_degree G (c := c) (d := d) hcard j
  · intro k hk
    have hka : k ∈ active c := by
      have hja := (mem_active _ _).mp hj
      simp only [mem_active]; exact lt_trans hk hja
    have hkd : k ∈ active d := by simp only [mem_active,d]; have := hk; change k.val < j.val at this; omega
    simp only [hkd,hka,if_true]
    exact congrArg Finset.card (hbeq k hk)
  · have hjd : j ∈ active d := by simp [d]
    simp only [hjd,hj,if_true]
    change (blockers G S' (c.vertex j)).card < (blockers G c.S (c.vertex j)).card
    rw [hb j le_rfl]
    exact card_erase_lt_of_mem hy

theorem exists_full (Δ : ℕ) (hd : DegreeLE G Δ)
    (hsurj : Function.Surjective part)
    (hsize : ∀ i, 2 * Δ ≤ Fintype.card {v // part v = i}) :
    ∃ S : Finset V, Partial G part S ∧ ∀ i, i ∈ S.image part := by
  by_cases hV : Nonempty V
  · letI := hV
    let emptyConfig : Config (V := V) := ⟨∅,0,fun _ => Classical.arbitrary V⟩
    have he : Valid G part emptyConfig := by
      refine ⟨Partial.empty G part,?_,?_,?_⟩ <;> simp [active,emptyConfig]
    obtain ⟨c,hc,hmin⟩ := Set.exists_min_image {c | Valid G part c} (score G)
      (Set.toFinite _) ⟨emptyConfig,he⟩
    refine ⟨c.S,hc.1,?_⟩
    by_contra! hmiss
    have hlast : ∃ j ∈ active c, (blockers G c.S (c.vertex j)) = ∅ := by
      by_contra! hn
      have hp : ∀ j ∈ active c, (blockers G c.S (c.vertex j)).Nonempty :=
        fun j hj => hn j hj
      have hlen : c.count.val < Fintype.card V := by
        have h1 := Valid.count_le_blocked G part hc hp
        have h2 := card_le_card (blocked_subset G c)
        have h3 := incomplete_card_lt part c.S hsurj hmiss
        omega
      obtain ⟨v,hv,ha,hb⟩ := extend_vertex G part Δ hd hsurj hsize hc hmiss hp
      have hdv := append_valid G part hc hlen v hv ha hb hp
      exact (not_lt_of_ge (hmin _ hdv)) (append_score G c hlen v)
    obtain ⟨l,hl,hlzero⟩ := hlast
    have hfree : ∀ z ∈ c.S, ¬ G.Adj (c.vertex l) z := by
      intro z hz hadj
      have hh : z ∈ blockers G c.S (c.vertex l) := mem_filter.mpr ⟨hz,hadj⟩
      rw [hlzero] at hh
      exact notMem_empty _ hh
    rcases hc.2.1 l hl with hav | ⟨j,hjl,y,hy,hyp⟩
    · let d : Config (V := V) := ⟨insert (c.vertex l) c.S,0,c.vertex⟩
      have hdv : Valid G part d := by
        refine ⟨Partial.insert_vertex G part hc.1 hav hfree,?_,?_,?_⟩ <;> simp [active,d]
      have hv : c.vertex l ∉ c.S := by intro h; exact hav (mem_image.mpr ⟨_,h,rfl⟩)
      have hinc : c.S.card < d.S.card := by simp [d,card_insert_of_notMem hv]
      exact (not_lt_of_ge (hmin _ hdv)) (score_card G hinc)
    · have hja : j ∈ active c := by
        have hla := (mem_active _ _).mp hl
        simp only [mem_active]; exact lt_trans hjl hla
      obtain ⟨d,hdv,hs⟩ := swap_improves G part hc j hja (c.vertex l) y hy hyp.symm hfree
        (fun k hk => (hc.2.2.1 l hl k (lt_of_le_of_lt hk hjl)).1)
      exact (not_lt_of_ge (hmin _ hdv)) hs
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    refine ⟨∅,Partial.empty G part,?_⟩
    intro i
    obtain ⟨v,_⟩ := hsurj i
    exact isEmptyElim v

end HaxellProof

/-- Haxell's independent transversal theorem, proved by finite lexicographic
minimization of augmenting sequences. Surjectivity handles empty degree bounds. -/
theorem haxell : Haxell := by
  intro V I _ _ G part Δ hsurj hd hsize
  obtain ⟨S,hS,hfull⟩ := HaxellProof.exists_full G part Δ hd hsurj hsize
  have hex : ∀ i, ∃ v ∈ S, part v = i := fun i => Finset.mem_image.mp (hfull i)
  choose f hf hp using hex
  exact ⟨f,hp,fun i j _ => hS.2 (f i) (hf i) (f j) (hf j)⟩
end Se20Part
