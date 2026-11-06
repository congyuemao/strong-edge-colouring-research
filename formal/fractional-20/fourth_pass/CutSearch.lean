import fourth_pass.PackedSoundness

namespace Se20Fractional.FourthPass

/-- Keep the positions marked by the low bits of a mask. -/
def retain {α : Type} : Nat → List α → List α
  | _, [] => []
  | k, a::as => if k % 2 == 1 then a :: retain (k/2) as else retain (k/2) as

/-- Only discarded elements require a computational rejection proof. -/
def cutCheck {α σ : Type} (possible : σ → α → Bool) (st : σ) : Nat → List α → Bool
  | _, [] => true
  | k, a::as => (k % 2 == 1 || !possible st a) && cutCheck possible st (k/2) as

theorem cut_preserves_good {α σ μ : Type} (possible : σ → α → Bool)
    (realizes : σ → μ → Prop) (good : μ → α → Bool)
    (hp : ∀ st m a, realizes st m → good m a = true → possible st a = true)
    (st : σ) (m : μ) (hm : realizes st m) (cs : List α) (k : Nat)
    (hc : cutCheck possible st k cs = true) :
    cs.filter (good m) = (retain k cs).filter (good m) := by
  induction cs generalizing k with
  | nil => rfl
  | cons a cs ih =>
    simp only [cutCheck,Bool.and_eq_true] at hc
    by_cases hk : k % 2 == 1
    · simpa only [retain,hk,↓reduceIte,List.filter_cons,ih _ hc.2]
    · have hfalse : possible st a = false := by simpa [hk] using hc.1
      have hg : good m a = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have htrue := hp st m a hm h
        simp [hfalse] at htrue
      simp only [retain,hk,↓reduceIte,List.filter_cons,hg,Bool.false_eq_true]
      exact ih _ hc.2

namespace Packed

def Safe (n d need : Nat) (st : Option State) (cs : List Edge) : Prop :=
  ∀ full, Realizes n d st full →
    (cs.filter (fun e => decide (e ∈ full.chosen))).length < need

theorem possible_of_realizes (n d : Nat) (st : Option State) (full : State) (e : Edge)
    (hm : Realizes n d st full) (he : decide (e ∈ full.chosen) = true) :
    possible n d st e = true := by
  obtain ⟨hmodel,s,rfl,hs⟩ := hm
  obtain ⟨next,hn,_⟩ := extend_sound hmodel s hs (of_decide_eq_true he)
  simp [possible,hn]

theorem step_realizes (n d : Nat) (st : Option State) (full : State) (e : Edge)
    (hm : Realizes n d st full) (he : decide (e ∈ full.chosen) = true) :
    Realizes n d (step n d st e) full := by
  obtain ⟨hmodel,s,rfl,hs⟩ := hm
  obtain ⟨next,hn,hns⟩ := extend_sound hmodel s hs (of_decide_eq_true he)
  exact ⟨hmodel,next,by simp [step,hn],hns⟩

theorem safe_prune (n d need : Nat) (st : Option State) (cs : List Edge)
    (hc : cs.length < need) : Safe n d need st cs := by
  intro full _
  exact (List.length_filter_le _ _).trans_lt hc

theorem safe_none (n d need : Nat) (cs : List Edge) : Safe n d need none cs := by
  rintro full ⟨_,s,h,_⟩
  cases h

theorem safe_invalid (n d need : Nat) (st : State) (cs : List Edge)
    (hv : valid n st = false) : Safe n d need (some st) cs := by
  rintro full ⟨hm,s,he,hs⟩
  have he' : st = s := Option.some.inj he
  subst s
  have ht := hs.valid hm
  simp [hv] at ht

theorem safe_cut (n d need : Nat) (st : Option State) (cs vs : List Edge) (k : Nat)
    (hc : cutCheck (possible n d) st k cs = true) (hv : retain k cs = vs)
    (hs : Safe n d need st vs) : Safe n d need st cs := by
  intro full hm
  have hfilter := cut_preserves_good (possible n d) (Realizes n d)
    (fun full e => decide (e ∈ full.chosen)) (possible_of_realizes n d) st full hm cs k hc
  rw [hfilter,hv]
  exact hs full hm

theorem safe_split (n d need : Nat) (st next : Option State) (a : Edge) (rest : List Edge)
    (hn : need ≠ 0) (he : step n d st a = next)
    (hskip : Safe n d need st rest) (htake : Safe n d (need-1) next rest) :
    Safe n d need st (a::rest) := by
  intro full hm
  by_cases ha : a ∈ full.chosen
  · have hnext := step_realizes n d st full a hm (by simp [ha])
    rw [he] at hnext
    have hi := htake full hnext
    simp only [List.filter_cons,ha,decide_true,↓reduceIte,List.length_cons]
    omega
  · simpa [ha] using hskip full hm

end Packed
end Se20Fractional.FourthPass
