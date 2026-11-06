import fourth_pass.ForcedTypes
import fourth_pass.SplitSafe

namespace Se20Fractional.FourthPass.Packed
open Lean Meta Elab Tactic

private def checkedProfile (type value : Expr) : MetaM Expr := do
  let name ← withOptions (fun o => o.setBool `Elab.async false) <| mkAuxLemma [] type value
  return mkConst name

private partial def profileProof (d s m : Nat) (pre : List Nat) (lower remaining : Nat)
    (profiles nodes : IO.Ref Nat) : MetaM Expr := do
  let label := "cert_" ++ toString d ++ "_" ++ toString s ++ "_" ++ toString m ++
    String.join (pre.map (fun t => "_" ++ toString t))
  let refName := `Se20Fractional.FourthPass.Packed ++ Name.mkSimple label
  if (← getEnv).contains refName then
    let fact := mkConst refName
    let expected ← mkAppM ``CompletionFree
      #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,toExpr remaining]
    if ← isDefEq (← inferType fact) expected then return fact
  profiles.modify (·+1)
  let st : State := ⟨profileGraph d m pre,rootChosen s⟩
  let args := #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,toExpr remaining]
  if !valid 14 st then
    let hve := mkApp2 (mkConst ``valid) (toExpr (14 : Nat)) (toExpr st)
    let hv ← checkedProfile (← mkEq hve (toExpr false)) (← mkEqRefl (toExpr false))
    let proof ← mkAppM ``completion_invalid (args.push hv)
    return ← checkedProfile (← inferType proof) proof
  if remaining > 0 && forcedType d lower > 0 then
    let forced : State := ⟨profileGraph d m (pre ++ List.replicate remaining (forcedType d lower)),
      rootChosen s⟩
    if !valid 14 forced then
      let hve := mkApp2 (mkConst ``valid) (toExpr (14 : Nat)) (toExpr forced)
      let hv ← checkedProfile (← mkEq hve (toExpr false)) (← mkEqRefl (toExpr false))
      let proof ← mkAppM ``completion_forced_invalid (args.push hv)
      return ← checkedProfile (← inferType proof) proof
  if remaining == 0 then
    let cs := candidates 14 d s st.graph pre
    let hs ← safeProof 14 d (16-s) (some st) cs nodes
    let proof ← mkAppM ``completion_leaf #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,hs]
    return ← checkedProfile (← inferType proof) proof
  let mut all ← mkAppM ``branches_base
    #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,toExpr (remaining-1)]
  for t in [lower:2^d] do
    let ht ← profileProof d s m (pre++[t]) t (remaining-1) profiles nodes
    all ← mkAppM ``branches_step
      #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,toExpr (remaining-1),toExpr t,all,ht]
    all ← checkedProfile (← inferType all) all
  let proof ← mkAppM ``completion_split
    #[toExpr d,toExpr s,toExpr m,toExpr pre,toExpr lower,toExpr (remaining-1),all]
  checkedProfile (← inferType proof) proof

unsafe def evalSplitProfiles : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.getType
  unless ty.isAppOfArity ``CompletionFree 6 do throwError "Expected CompletionFree"
  let a := ty.getAppArgs
  let d ← evalExpr Nat (toTypeExpr Nat) a[0]!
  let s ← evalExpr Nat (toTypeExpr Nat) a[1]!
  let m ← evalExpr Nat (toTypeExpr Nat) a[2]!
  let pre ← evalExpr (List Nat) (toTypeExpr (List Nat)) a[3]!
  let lower ← evalExpr Nat (toTypeExpr Nat) a[4]!
  let remaining ← evalExpr Nat (toTypeExpr Nat) a[5]!
  let profiles ← IO.mkRef 0
  let nodes ← IO.mkRef 0
  let proof ← profileProof d s m pre lower remaining profiles nodes
  goal.assign proof
  logInfo m!"Kernel-checked profile nodes: {← profiles.get}; selection nodes: {← nodes.get}"
  replaceMainGoal []

elab "split_profiles" : tactic => unsafe evalSplitProfiles
end Se20Fractional.FourthPass.Packed
