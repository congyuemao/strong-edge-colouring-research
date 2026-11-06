import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_4_0_0_1_4 : CompletionFree 4 4 0 [0,1,4] 4 6 := by split_profiles
theorem cert_4_4_0_0_1_5 : CompletionFree 4 4 0 [0,1,5] 5 6 := by split_profiles
theorem cert_4_4_0_0_1_6 : CompletionFree 4 4 0 [0,1,6] 6 6 := by split_profiles
theorem cert_4_4_0_0_1_7 : CompletionFree 4 4 0 [0,1,7] 7 6 := by split_profiles
theorem cert_4_4_0_0_1_8 : CompletionFree 4 4 0 [0,1,8] 8 6 := by split_profiles
theorem cert_4_4_0_0_1_9 : CompletionFree 4 4 0 [0,1,9] 9 6 := by split_profiles
theorem cert_4_4_0_0_1_10 : CompletionFree 4 4 0 [0,1,10] 10 6 := by split_profiles
theorem cert_4_4_0_0_1_11 : CompletionFree 4 4 0 [0,1,11] 11 6 := by split_profiles
theorem cert_4_4_0_0_1_12 : CompletionFree 4 4 0 [0,1,12] 12 6 := by split_profiles
theorem cert_4_4_0_0_1_13 : CompletionFree 4 4 0 [0,1,13] 13 6 := by split_profiles
theorem cert_4_4_0_0_1_14 : CompletionFree 4 4 0 [0,1,14] 14 6 := by split_profiles
theorem cert_4_4_0_0_1_15 : CompletionFree 4 4 0 [0,1,15] 15 6 := by split_profiles
theorem cert_4_4_0_0_2_2_2 : CompletionFree 4 4 0 [0,2,2,2] 2 5 := by split_profiles
theorem cert_4_4_0_0_2_2_3 : CompletionFree 4 4 0 [0,2,2,3] 3 5 := by split_profiles
theorem cert_4_4_0_0_2_2_4 : CompletionFree 4 4 0 [0,2,2,4] 4 5 := by split_profiles
end Se20Fractional.FourthPass.Packed
