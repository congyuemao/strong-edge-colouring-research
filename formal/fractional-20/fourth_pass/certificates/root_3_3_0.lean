import fourth_pass.certificates.group_3_3_0_0
import fourth_pass.certificates.group_3_3_0_1
import fourth_pass.certificates.group_3_3_0_2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Se20Fractional.FourthPass.Packed
theorem root_3_3_0 : CompletionFree 3 3 0 [] 0 10 := by split_profiles
#print axioms root_3_3_0
end Se20Fractional.FourthPass.Packed
