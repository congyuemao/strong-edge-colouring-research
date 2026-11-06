import fourth_pass.SplitSafe
open Se20Fractional.FourthPass.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def safeFrozen : State := ⟨23376750291353229814239710164813854,[(0,1),(0,2),(0,3)]⟩
def safeCandidates : List Edge := [(1,8),(1,9),(1,10),(2,5),(2,6),(2,7),
  (3,5),(3,6),(3,7),(4,8),(4,9),(4,10),(5,8),(5,9),(5,10),
  (6,8),(6,9),(6,10),(7,8),(7,9),(7,10)]
theorem frozen_safe : Safe 11 4 13 (some safeFrozen) safeCandidates := by split_safe
#print axioms frozen_safe
