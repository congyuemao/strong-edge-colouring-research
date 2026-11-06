import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_3_0_0_1_1_1 : CompletionFree 4 3 0 [0,1,1,1] 1 5 := by split_profiles
theorem cert_4_3_0_0_1_1_2_2 : CompletionFree 4 3 0 [0,1,1,2,2] 2 4 := by split_profiles
theorem cert_4_3_0_0_1_1_2_3 : CompletionFree 4 3 0 [0,1,1,2,3] 3 4 := by split_profiles
theorem cert_4_3_0_0_1_1_2_4 : CompletionFree 4 3 0 [0,1,1,2,4] 4 4 := by split_profiles
theorem cert_4_3_0_0_1_1_2_5 : CompletionFree 4 3 0 [0,1,1,2,5] 5 4 := by split_profiles
end Se20Fractional.FourthPass.Packed
