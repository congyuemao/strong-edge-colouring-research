import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_3_3_0_0_0_0_0_0_0_0 : CompletionFree 3 3 0 [0,0,0,0,0,0,0] 0 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_1 : CompletionFree 3 3 0 [0,0,0,0,0,0,1] 1 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_2 : CompletionFree 3 3 0 [0,0,0,0,0,0,2] 2 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_3 : CompletionFree 3 3 0 [0,0,0,0,0,0,3] 3 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_4 : CompletionFree 3 3 0 [0,0,0,0,0,0,4] 4 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_5 : CompletionFree 3 3 0 [0,0,0,0,0,0,5] 5 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_6 : CompletionFree 3 3 0 [0,0,0,0,0,0,6] 6 3 := by split_profiles
theorem cert_3_3_0_0_0_0_0_0_0_7 : CompletionFree 3 3 0 [0,0,0,0,0,0,7] 7 3 := by split_profiles
end Se20Fractional.FourthPass.Packed
