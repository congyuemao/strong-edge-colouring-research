import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_3_0_0_0_0_0_0_0 : CompletionFree 4 3 0 [0,0,0,0,0,0] 0 3 := by split_profiles
theorem cert_4_3_0_0_0_0_0_0_1 : CompletionFree 4 3 0 [0,0,0,0,0,1] 1 3 := by split_profiles
end Se20Fractional.FourthPass.Packed
