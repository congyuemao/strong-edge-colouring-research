import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem profile_bench : CompletionFree 3 3 0 [0,0,0,0] 0 6 := by split_profiles
#print axioms profile_bench
end Se20Fractional.FourthPass.Packed
