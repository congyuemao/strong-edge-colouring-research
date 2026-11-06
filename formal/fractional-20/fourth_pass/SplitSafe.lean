import fourth_pass.ReorderSafe
import fourth_pass.SplitSearch

namespace Se20Fractional.FourthPass.Packed
open Lean Meta Elab Tactic

private def checked (type value : Expr) : MetaM Expr := do
  let name ← withOptions (fun o => o.setBool `Elab.async false) <| mkAuxLemma [] type value
  return mkConst name
private def checkedDecide (type : Expr) : MetaM Expr := do checked type (← mkDecideProof type)
private def checkedEq (lhs rhs : Expr) : MetaM Expr := do checked (← mkEq lhs rhs) (← mkEqRefl rhs)

partial def safeProof (n d need : Nat) (st : Option State) (cs : List Edge)
    (counter : IO.Ref Nat) : MetaM Expr := do
  counter.modify (·+1)
  if need == 0 then throwError "Open selection leaf"
  if cs.length < need then
    let hc ← checkedDecide (← mkLt (← mkAppM ``List.length #[toExpr cs]) (toExpr need))
    return ← checked (← mkAppM ``Safe #[toExpr n,toExpr d,toExpr need,toExpr st,toExpr cs])
      (← mkAppM ``safe_prune #[toExpr n,toExpr d,toExpr need,toExpr st,toExpr cs,hc])
  if st.isNone then
    return ← mkAppM ``safe_none #[toExpr n,toExpr d,toExpr need,toExpr cs]
  let keep := (cs.zipIdx).foldl (fun k (a,i) => if possible n d st a then k ||| bit i else k) 0
  let vs := retain keep cs
  let pivot := if vs.length < need then 0 else
    ((vs.zipIdx).foldl (fun best (e,i) =>
      let next := step n d st e
      let score := (vs.filter (fun f => f != e && possible n d next f)).length
      if score < best.1 then (score,i) else best) (vs.length+1,0)).2
  let pre := vs.take pivot
  let post := vs.drop (pivot+1)
  let ws := if pivot == 0 then vs else vs[pivot]! :: (pre ++ post)
  let stE := toExpr st
  let vsE := toExpr vs
  let wsE := toExpr ws
  let result ← if ws.length < need then do
    let hc ← checkedDecide (← mkLt (← mkAppM ``List.length #[wsE]) (toExpr need))
    mkAppM ``safe_prune #[toExpr n,toExpr d,toExpr need,stE,wsE,hc]
  else match ws with
    | [] => throwError "Empty viable list"
    | a::rest => do
      let next := step n d st a
      let he ← checkedEq (mkApp4 (mkConst ``step) (toExpr n) (toExpr d) stE (toExpr a)) (toExpr next)
      let hn ← checkedDecide (mkNot (← mkEq (toExpr need) (toExpr (0 : Nat))))
      let hskip ← safeProof n d need st rest counter
      let htake ← safeProof n d (need-1) next rest counter
      mkAppM ``safe_split #[toExpr n,toExpr d,toExpr need,stE,toExpr next,toExpr a,toExpr rest,
        hn,he,hskip,htake]
  let result ← checked (← inferType result) result
  let result ← if pivot == 0 then pure result else do
    let proof ← mkAppM ``safe_rotate
      #[toExpr n,toExpr d,toExpr need,stE,toExpr pre,toExpr vs[pivot]!,toExpr post,result]
    checked (← mkAppM ``Safe #[toExpr n,toExpr d,toExpr need,stE,vsE]) proof
  if keep == bit cs.length - 1 then
    return result
  else
    let p := mkApp2 (mkConst ``possible) (toExpr n) (toExpr d)
    let hcExpr ← mkAppM ``cutCheck #[p,stE,toExpr keep,toExpr cs]
    let hc ← checkedEq hcExpr (toExpr true)
    let hv ← checkedEq (← mkAppM ``retain #[toExpr keep,toExpr cs]) vsE
    let result ← mkAppM ``safe_cut #[toExpr n,toExpr d,toExpr need,stE,toExpr cs,vsE,toExpr keep,
      hc,hv,result]
    checked (← inferType result) result

unsafe def evalSplitSafe : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.getType
  unless ty.isAppOfArity ``Safe 5 do throwError "Expected Packed.Safe"
  let a := ty.getAppArgs
  let n ← evalExpr Nat (toTypeExpr Nat) a[0]!
  let d ← evalExpr Nat (toTypeExpr Nat) a[1]!
  let need ← evalExpr Nat (toTypeExpr Nat) a[2]!
  let st ← evalExpr (Option State) (toTypeExpr (Option State)) a[3]!
  let cs ← evalExpr (List Edge) (toTypeExpr (List Edge)) a[4]!
  let counter ← IO.mkRef 0
  let proof ← safeProof n d need st cs counter
  goal.assign proof
  logInfo m!"Kernel-checked safe nodes: {← counter.get}"
  replaceMainGoal []

elab "split_safe" : tactic => unsafe evalSplitSafe
end Se20Fractional.FourthPass.Packed
