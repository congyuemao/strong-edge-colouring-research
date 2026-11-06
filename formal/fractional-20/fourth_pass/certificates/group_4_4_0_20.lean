import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_4_0_0_4 : CompletionFree 4 4 0 [0,4] 4 7 := by split_profiles
theorem cert_4_4_0_0_5 : CompletionFree 4 4 0 [0,5] 5 7 := by split_profiles
theorem cert_4_4_0_0_6 : CompletionFree 4 4 0 [0,6] 6 7 := by split_profiles
theorem cert_4_4_0_0_7 : CompletionFree 4 4 0 [0,7] 7 7 := by split_profiles
theorem cert_4_4_0_0_8 : CompletionFree 4 4 0 [0,8] 8 7 := by split_profiles
theorem cert_4_4_0_0_9 : CompletionFree 4 4 0 [0,9] 9 7 := by split_profiles
theorem cert_4_4_0_0_10 : CompletionFree 4 4 0 [0,10] 10 7 := by split_profiles
theorem cert_4_4_0_0_11 : CompletionFree 4 4 0 [0,11] 11 7 := by split_profiles
theorem cert_4_4_0_0_12 : CompletionFree 4 4 0 [0,12] 12 7 := by split_profiles
theorem cert_4_4_0_0_13 : CompletionFree 4 4 0 [0,13] 13 7 := by split_profiles
theorem cert_4_4_0_0_14 : CompletionFree 4 4 0 [0,14] 14 7 := by split_profiles
theorem cert_4_4_0_0_15 : CompletionFree 4 4 0 [0,15] 15 7 := by split_profiles
theorem cert_4_4_0_1_1_1 : CompletionFree 4 4 0 [1,1,1] 1 6 := by split_profiles
end Se20Fractional.FourthPass.Packed
