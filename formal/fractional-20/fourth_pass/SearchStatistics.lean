import fourth_pass.PackedSearch

/-! Compiled diagnostic statistics only: no acceptance theorem is asserted. -/
namespace Se20Fractional.FourthPass.Packed

def selectionStats {α σ : Type} (possible : σ → α → Bool) (step : σ → α → σ) :
    Nat → Nat → σ → List α → Bool × Nat
  | 0, _, _, _ => (false,1)
  | fuel+1, need, st, cs =>
    if need = 0 then (false,1) else
    let vs := cs.filter (possible st)
    if vs.length < need then (true,1) else
    match vs with
    | [] => (true,1)
    | e::es =>
      let skip := selectionStats possible step fuel need st es
      if !skip.1 then (false,skip.2+1) else
      let take := selectionStats possible step fuel (need-1) (step st e) es
      (take.1,skip.2+take.2+1)

structure Counts where
  profiles : Nat := 0
  baseValid : Nat := 0
  initialViable : Nat := 0
  nodes : Nat := 0
  openProfiles : Nat := 0
  deriving Repr

def addCounts (a b : Counts) : Counts :=
  ⟨a.profiles+b.profiles,a.baseValid+b.baseValid,a.initialViable+b.initialViable,
    a.nodes+b.nodes,a.openProfiles+b.openProfiles⟩

def innerGraph (n d m : Nat) : Nat :=
  (((pairs (d+1)).filter (fun e => 0 < e.1)).zipIdx).foldl
    (fun h (e,i) => if (m &&& bit i) != 0 then addEdge n h e else h) 0

def profileStats (d s m : Nat) (ts : List Nat) : Counts :=
  let n := d+1+ts.length
  let h := typeGraph n d ts ||| innerGraph n d m
  let st : State := ⟨h,rootChosen s⟩
  if !valid n st then ⟨1,0,0,0,0⟩ else
  let cs := candidates n d s h ts
  let vs := cs.filter (possible n d (some st))
  if vs.length < 16-s then ⟨1,1,0,1,0⟩ else
  let result := selectionStats (possible n d) (step n d) 92 (16-s) (some st) cs
  ⟨1,1,1,result.2,if result.1 then 0 else 1⟩

def typeStats (d s m : Nat) : Nat → Nat → List Nat → List Nat → Nat → Nat → Counts
  | fuel,last,ts,cap,zeros,triples =>
    let here := if zeros ≤ triples then profileStats d s m ts else defaultCounts
    match fuel with
    | 0 => here
    | k+1 =>
      ((List.range (bit d)).filter (fun t => last ≤ t)).foldl (fun total t =>
        if (t == 0 && s == 4) ||
            !(cap.zipIdx).all (fun (c,a) => (t &&& bit a) == 0 || 0 < c) then total else
        let cap' := (cap.zipIdx).map (fun (c,a) => c - if (t &&& bit a) != 0 then 1 else 0)
        addCounts total (typeStats d s m k t (ts++[t]) cap'
          (zeros+if t == 0 then 1 else 0) (triples+if 3 ≤ pop d t then 1 else 0))) here
where
  defaultCounts : Counts := ⟨0,0,0,0,0⟩

def rootStats (d s maxOuter : Nat) : Counts :=
  (List.range (bit (d*(d-1)/2))).foldl (fun total m =>
    let n := d+1
    let h := rootGraph n d ||| innerGraph n d m
    if !valid n ⟨h,rootChosen s⟩ then total else
    let cap := (List.range d).map (fun a => 4-pop n (row n h (a+1)))
    addCounts total (typeStats d s m maxOuter 0 [] cap 0 0)) ⟨0,0,0,0,0⟩

end Se20Fractional.FourthPass.Packed
