import fourth_pass.SplitSearch
open Se20Fractional.FourthPass Se20Fractional.FourthPass.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def frozen : State := ⟨23376750291353229814239710164813854, [(0,1),(0,2),(0,3)]⟩
def frozenCandidates : List Edge := [(1,8),(1,9),(1,10),(2,5),(2,6),(2,7),
  (3,5),(3,6),(3,7),(4,8),(4,9),(4,10),(5,8),(5,9),(5,10),
  (6,8),(6,9),(6,10),(7,8),(7,9),(7,10)]

theorem frozen_graph : typeGraph 11 4 [6,6,6,9,9,9] = frozen.graph := by decide +kernel
theorem frozen_initial :
    frozenCandidates.filter (possible 11 4 (some frozen)) = frozenCandidates := by decide +kernel
#print axioms frozen_initial

def searchStats {α σ : Type} (possible : σ → α → Bool) (step : σ → α → σ) :
    Nat → Nat → σ → List α → Bool × Nat
  | 0, _, _, _ => (false,1)
  | fuel+1, need, st, cs =>
    if need = 0 then (false,1) else
    let vs := cs.filter (possible st)
    if vs.length < need then (true,1) else
    match vs with
    | [] => (true,1)
    | e::es =>
      let skip := searchStats possible step fuel need st es
      if !skip.1 then (false,skip.2+1) else
      let take := searchStats possible step fuel (need-1) (step st e) es
      (take.1,skip.2+take.2+1)
#eval searchStats (possible 11 4) (step 11 4) 92 13 (some frozen) frozenCandidates

theorem frozen_checked :
    selectionSearch (possible 11 4) (step 11 4) 92 13 (some frozen) frozenCandidates = true :=
  by split_selection
#print axioms frozen_checked
