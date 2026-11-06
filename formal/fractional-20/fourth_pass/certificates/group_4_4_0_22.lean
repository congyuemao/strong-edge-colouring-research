import fourth_pass.SplitProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem cert_4_4_0_1_2_2 : CompletionFree 4 4 0 [1,2,2] 2 6 := by split_profiles
theorem cert_4_4_0_1_2_3 : CompletionFree 4 4 0 [1,2,3] 3 6 := by split_profiles
theorem cert_4_4_0_1_2_4 : CompletionFree 4 4 0 [1,2,4] 4 6 := by split_profiles
theorem cert_4_4_0_1_2_5 : CompletionFree 4 4 0 [1,2,5] 5 6 := by split_profiles
end Se20Fractional.FourthPass.Packed
