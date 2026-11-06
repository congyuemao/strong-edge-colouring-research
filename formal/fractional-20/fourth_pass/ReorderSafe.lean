import fourth_pass.CutSearch
import Mathlib.Data.List.Perm.Basic

namespace Se20Fractional.FourthPass.Packed
theorem safe_perm (n d need : Nat) (st : Option State) (cs vs : List Edge)
    (hp : cs.Perm vs) (hs : Safe n d need st vs) : Safe n d need st cs := by
  intro full hm
  rw [(hp.filter (fun e => decide (e ∈ full.chosen))).length_eq]
  exact hs full hm

example : [(1,2),(3,4)].Perm ([(3,4),(1,2)] : List Edge) := by decide

theorem safe_rotate (n d need : Nat) (st : Option State) (pre : List Edge) (a : Edge)
    (post : List Edge) (hs : Safe n d need st (a :: (pre ++ post))) :
    Safe n d need st (pre ++ a :: post) := by
  apply safe_perm n d need st _ _ _ hs
  exact List.perm_middle
end Se20Fractional.FourthPass.Packed
