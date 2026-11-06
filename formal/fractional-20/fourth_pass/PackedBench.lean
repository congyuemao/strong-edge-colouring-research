import fourth_pass.PackedSearch
open Se20Fractional.FourthPass.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#eval checkProfile 4 3 0 [6,6,6,9,9,9]

theorem profile_small : checkProfile 3 3 0 [1,1,6,6,6] = true := by decide +kernel
#print axioms profile_small

