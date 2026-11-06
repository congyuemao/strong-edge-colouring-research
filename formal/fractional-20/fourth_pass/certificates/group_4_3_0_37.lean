import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_3_0_1_1_1 : CompletionFree 4 3 0 [1,1,1] 1 6 := by split_profiles
theorem cert_4_3_0_1_1_2_2 : CompletionFree 4 3 0 [1,1,2,2] 2 5 := by split_profiles
theorem cert_4_3_0_1_1_2_3 : CompletionFree 4 3 0 [1,1,2,3] 3 5 := by split_profiles
theorem cert_4_3_0_1_1_2_4 : CompletionFree 4 3 0 [1,1,2,4] 4 5 := by split_profiles
theorem cert_4_3_0_1_1_2_5 : CompletionFree 4 3 0 [1,1,2,5] 5 5 := by split_profiles
theorem cert_4_3_0_1_1_2_6 : CompletionFree 4 3 0 [1,1,2,6] 6 5 := by split_profiles
end Se20Fractional.FourthPass.Packed
