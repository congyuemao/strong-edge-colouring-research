import fourth_pass.ProfileEnumeration
open Se20Fractional.FourthPass.Packed
#eval innerPairs 4
#eval (List.range 64).filter (fun m => valid 14 ⟨profileGraph 4 m [], rootChosen 3⟩ && (innerEdges 4 m).all (fun e => decide (3 < e.2)))
#eval (List.range 8).filter (fun m => valid 14 ⟨profileGraph 3 m [], rootChosen 3⟩ && (innerEdges 3 m).all (fun e => decide (3 < e.2)))
