import fourth_pass.certificates.group_4_3_4_0
import fourth_pass.certificates.group_4_3_4_1
import fourth_pass.certificates.group_4_3_4_2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem root_4_3_4 : CompletionFree 4 3 4 [] 0 9 := by split_profiles
#print axioms root_4_3_4
end Se20Fractional.FourthPass.Packed
