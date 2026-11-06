import Se20Part.TreeLemma

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
namespace TreeBall
set_option maxHeartbeats 2000000

variable {V : Type} {G : SimpleGraph V}

local instance forwardFintype [G.LocallyFinite] (u v : V) : Fintype (Forward G u v) :=
  Fintype.ofInjective (fun w : Forward G u v => (⟨w.val,w.property.1⟩ : G.neighborSet v))
    (fun _ _ h => Subtype.ext (congrArg (fun x : G.neighborSet v => x.val) h))

theorem forward_card [G.LocallyFinite] (hd : ∀ v, G.degree v = 4) {u v : V}
    (huv : G.Adj u v) : Fintype.card (Forward G u v) = 3 := by
  let eqv : Forward G u v ≃ {w : G.neighborSet v // w ≠ ⟨u,huv.symm⟩} :=
    { toFun := fun w => ⟨⟨w.val,w.property.1⟩,fun he => w.property.2 (congrArg Subtype.val he)⟩
      invFun := fun w => ⟨w.val.val,w.val.property,fun he => w.property (Subtype.ext he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr eqv]
  simp [G.card_neighborSet_eq_degree,hd]

@[reducible] def Code (G : SimpleGraph V) : ℕ → V → V → Type _
  | 0, _, _ => Empty
  | n+1, u, v => Σ w : Forward G u v, Option (Code G n v w.val)

@[reducible] instance codeFintype [G.LocallyFinite] : ∀ n u v, Fintype (Code G n u v)
  | 0, _, _ => inferInstanceAs (Fintype Empty)
  | n+1, u, v => by
      letI : ∀ w : Forward G u v, Fintype (Code G n v w.val) := fun w => codeFintype n v w.val
      exact inferInstanceAs (Fintype (Σ w : Forward G u v, Option (Code G n v w.val)))

theorem code_card [G.LocallyFinite] (hd : ∀ v, G.degree v = 4) (n : ℕ) {u v : V}
    (huv : G.Adj u v) : Fintype.card (Code G n u v) = branchBound n := by
  induction n generalizing u v with
  | zero => simp [Code,branchBound]
  | succ n ih =>
    change Fintype.card (Σ w : Forward G u v, Option (Code G n v w.val)) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_option]
    have he : (∑ w : Forward G u v, (Fintype.card (Code G n v w.val)+1)) =
        ∑ _w : Forward G u v, (branchBound n+1) := by
      apply sum_congr rfl
      intro w _
      rw [ih w.property.1]
    rw [he]
    simp [forward_card hd huv,branchBound,Nat.add_comm]

def lastEdge {u v : V} (p : G.Walk u v) (hn : ¬ p.Nil) : G.edgeSet :=
  ⟨s(p.penultimate,v),p.adj_penultimate hn⟩

abbrev RootPath (G : SimpleGraph V) (u : V) :=
  Σ v : V, {p : G.Walk u v // p.IsPath ∧ ¬ p.Nil}

def pathEdge {u : V} (p : RootPath G u) : G.edgeSet := lastEdge p.2.val p.2.property.2

theorem pathEdge_injective (ht : G.IsAcyclic) (u : V) :
    Function.Injective (pathEdge (G := G) (u := u)) := by
  rintro ⟨v,p,hp,hn⟩ ⟨w,q,hq,hm⟩ he
  have he' : s(p.penultimate,v) = s(q.penultimate,w) := congrArg Subtype.val he
  have hvw : v = w := by
    rcases Sym2.eq_iff.mp he' with h | h
    · exact h.2
    · have hvq : v ∈ q.support := by rw [h.2]; exact q.getVert_mem_support (q.length-1)
      have hwp : w ∈ p.support := by rw [← h.1]; exact p.getVert_mem_support (p.length-1)
      have hadj : G.Adj v w := by simpa only [h.1] using (p.adj_penultimate hn).symm
      exact False.elim (ht.ne_mem_support_of_support_of_adj_of_isPath hp hq hadj hwp hvq)
  subst w
  have hpq : p = q := congrArg Subtype.val ((ht.subsingleton_path u v).elim ⟨p,hp⟩ ⟨q,hq⟩)
  subst q
  rfl

@[reducible] def codeEnd : {n : ℕ} → {u v : V} → Code G n u v → V
  | _+1, _, _, ⟨w,none⟩ => w.val
  | _+1, _, _, ⟨_,some c⟩ => codeEnd c

@[reducible] def codeWalk : {n : ℕ} → {u v : V} → (h : G.Adj u v) →
    (c : Code G n u v) → G.Walk u (codeEnd c)
  | _+1, _, _, h, ⟨w,none⟩ => Walk.cons h (Walk.cons w.property.1 Walk.nil)
  | _+1, _, _, h, ⟨w,some c⟩ => Walk.cons h (codeWalk w.property.1 c)

theorem codeWalk_snd {n : ℕ} {u v : V} (h : G.Adj u v) (c : Code G n u v) :
    (codeWalk h c).snd = v := by
  cases n with
  | zero => exact isEmptyElim c
  | succ n => rcases c with ⟨w,none|c⟩ <;> simp only [codeWalk,Walk.snd_cons]

theorem codeWalk_two {n : ℕ} {u v : V} (h : G.Adj u v) (c : Code G (n+1) u v) :
    (codeWalk h c).getVert 2 = c.1.val := by
  rcases c with ⟨w,none|c⟩
  · rfl
  · simpa only [codeWalk,Walk.getVert_cons_succ] using codeWalk_snd w.property.1 c

theorem codeWalk_length {n : ℕ} {u v : V} (h : G.Adj u v) (c : Code G n u v) :
    2 ≤ (codeWalk h c).length ∧ (codeWalk h c).length ≤ n+1 := by
  induction n generalizing u v with
  | zero => exact isEmptyElim c
  | succ n ih =>
    rcases c with ⟨w,none|c⟩
    · simp [codeWalk]
    · have hh := ih w.property.1 c
      simp only [codeWalk,Walk.length_cons]
      omega

theorem codeWalk_path (ht : G.IsAcyclic) {n : ℕ} {u v : V}
    (h : G.Adj u v) (c : Code G n u v) : (codeWalk h c).IsPath := by
  induction n generalizing u v with
  | zero => exact isEmptyElim c
  | succ n ih =>
    rcases c with ⟨w,none|c⟩
    · simp [codeWalk,Walk.cons_isPath_iff,h.ne,w.property.1.ne,Ne.symm w.property.2]
    · apply Walk.IsPath.cons (ih w.property.1 c)
      intro hu
      have he := ht.eq_snd_of_adj_start (ih w.property.1 c) h.symm hu
      rw [codeWalk_snd] at he
      exact w.property.2 he.symm

def codePath (ht : G.IsAcyclic) {n : ℕ} {u v : V} (h : G.Adj u v) (c : Code G n u v) :
    RootPath G u := ⟨codeEnd c,codeWalk h c,codeWalk_path ht h c,
      fun hz => by have := Walk.Nil.length_eq_zero hz; have := codeWalk_length h c; omega⟩

def codeEdge : {n : ℕ} → {u v : V} → Code G n u v → G.edgeSet
  | _+1, _, _, ⟨w,none⟩ => ⟨s(_,w.val),w.property.1⟩
  | _+1, _, _, ⟨_,some c⟩ => codeEdge c

theorem codeEdge_pathEdge (ht : G.IsAcyclic) {n : ℕ} {u v : V} (h : G.Adj u v)
    (c : Code G n u v) : codeEdge c = pathEdge (codePath ht h c) := by
  induction n generalizing u v with
  | zero => exact isEmptyElim c
  | succ n ih =>
    rcases c with ⟨w,none|c⟩
    · rfl
    · rw [codeEdge,ih w.property.1 c]
      apply Subtype.ext
      simp only [pathEdge,lastEdge,codePath,codeWalk]
      congr 1
      have hn : ¬ (codeWalk w.property.1 c).Nil := by
        intro hz; have := Walk.Nil.length_eq_zero hz; have := codeWalk_length w.property.1 c; omega
      rw [← Walk.cons_tail_eq (codeWalk w.property.1 c) hn,Walk.penultimate_cons_cons]

theorem codeEdge_injective (ht : G.IsAcyclic) (n : ℕ) {u v : V} (h : G.Adj u v) :
    Function.Injective (codeEdge (G := G) (n := n) (u := u) (v := v)) := by
  induction n generalizing u v with
  | zero => intro a; exact isEmptyElim a
  | succ n ih =>
    intro a b he
    have hp := pathEdge_injective ht u (by simpa only [← codeEdge_pathEdge] using he :
      pathEdge (codePath ht h a) = pathEdge (codePath ht h b))
    have hw : a.1 = b.1 := by
      apply Subtype.ext
      have hh := congrArg (fun p : RootPath G u => p.2.val.getVert 2) hp
      simpa only [codePath,codeWalk_two] using hh
    rcases a with ⟨w,a⟩
    rcases b with ⟨w',b⟩
    simp only at hw
    subst w'
    have hl := congrArg (fun p : RootPath G u => p.2.val.length) hp
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have := codeWalk_length w.property.1 b; simp only [codePath,codeWalk,Walk.length_cons,Walk.length_nil] at hl; omega
    | some a =>
      cases b with
      | none => have := codeWalk_length w.property.1 a; simp only [codePath,codeWalk,Walk.length_cons,Walk.length_nil] at hl; omega
      | some b => have hab := ih w.property.1 he; subst b; rfl

end TreeBall
end Se20Part
