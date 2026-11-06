import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_3_0_0_1_2_3 : CompletionFree 4 3 0 [0,1,2,3] 3 5 := by split_profiles
theorem cert_4_3_0_0_1_2_4_4 : CompletionFree 4 3 0 [0,1,2,4,4] 4 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_5 : CompletionFree 4 3 0 [0,1,2,4,5] 5 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_6 : CompletionFree 4 3 0 [0,1,2,4,6] 6 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_7 : CompletionFree 4 3 0 [0,1,2,4,7] 7 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_8 : CompletionFree 4 3 0 [0,1,2,4,8] 8 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_9 : CompletionFree 4 3 0 [0,1,2,4,9] 9 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_10 : CompletionFree 4 3 0 [0,1,2,4,10] 10 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_11 : CompletionFree 4 3 0 [0,1,2,4,11] 11 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_12 : CompletionFree 4 3 0 [0,1,2,4,12] 12 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_13 : CompletionFree 4 3 0 [0,1,2,4,13] 13 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_14 : CompletionFree 4 3 0 [0,1,2,4,14] 14 4 := by split_profiles
theorem cert_4_3_0_0_1_2_4_15 : CompletionFree 4 3 0 [0,1,2,4,15] 15 4 := by split_profiles
end Se20Fractional.FourthPass.Packed
