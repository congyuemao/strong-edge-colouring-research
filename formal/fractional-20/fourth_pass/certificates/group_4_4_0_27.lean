import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_4_0_6 : CompletionFree 4 4 0 [6] 6 8 := by split_profiles
theorem cert_4_4_0_7 : CompletionFree 4 4 0 [7] 7 8 := by split_profiles
theorem cert_4_4_0_8 : CompletionFree 4 4 0 [8] 8 8 := by split_profiles
theorem cert_4_4_0_9 : CompletionFree 4 4 0 [9] 9 8 := by split_profiles
theorem cert_4_4_0_10 : CompletionFree 4 4 0 [10] 10 8 := by split_profiles
theorem cert_4_4_0_11 : CompletionFree 4 4 0 [11] 11 8 := by split_profiles
theorem cert_4_4_0_12 : CompletionFree 4 4 0 [12] 12 8 := by split_profiles
theorem cert_4_4_0_13 : CompletionFree 4 4 0 [13] 13 8 := by split_profiles
theorem cert_4_4_0_14 : CompletionFree 4 4 0 [14] 14 8 := by split_profiles
theorem cert_4_4_0_15 : CompletionFree 4 4 0 [15] 15 8 := by split_profiles
end Se20Fractional.FourthPass.Packed
