import VIR
open VIR
-- STATUS-vir row 48: the POSITIVE CONTROL vir's Lean audit lacks, beside the same #print axioms rows (Audit.lean and out/ untouched).
theorem control_sorry : (1 : Nat) = 2 := sorry
#print axioms control_sorry
#print axioms router_fusion
#print axioms router_fusion_casesplit
#print axioms VIR.Flat.slice_fuse_flat
#print axioms VIR.Deep.router_fusion_deep
#print axioms VIR.Deep.router_fusion_deep_steps
#print axioms VIR.Deep.F_exit
#print axioms VIR.Deep.U_exit
#print axioms VIR.router2_fusion
#print axioms VIR.Deep2.router2_fusion_deep
#print axioms VIR.Deep2.router2_fusion_deep_steps
#print axioms VIR.Z.router2z_fusion
#print axioms VIR.Deep2.F2_exit
#print axioms VIR.Deep2.U2_exit
#print axioms VIR.Deep2S.router2s_fusion_deep
#print axioms VIR.Deep2S.router2s_fusion_deep_steps
#print axioms VIR.route_acl_safe
#print axioms VIR.route_acl_safe_flat
#print axioms VIR.Deep2.route_acl_safe_deep
