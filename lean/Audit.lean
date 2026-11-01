import VIR
open VIR
-- terms on the I4 path (scored chain): C1 reads this output
#print router_fusion
#print slice_fuse
#print Slice.congr_heq
#print Slice.adv_adv_heq
#print Slice.heq_of
#print guard_merge
#print beta_lin
#print aux_read_past_guard
#print aux_advance_past_guard
#print aux_guard_swap
-- axiom receipt: C4 reads this output
#print axioms router_fusion
#print axioms router_fusion_casesplit
#print VIR.Flat.slice_fuse_flat
#print axioms VIR.Flat.slice_fuse_flat
#print axioms VIR.Deep.router_fusion_deep
#print axioms VIR.Deep.router_fusion_deep_steps
#print axioms VIR.Deep.F_exit
#print axioms VIR.Deep.U_exit
#print VIR.router2_fusion
#print VIR.slice_fuse_dep
#print VIR.Slice.congr_heq_dep
#print VIR.aux_advance_idx
#print VIR.aux_advance_past_dguard
#print VIR.aux_guard_cond_eq
#print axioms VIR.router2_fusion
#print axioms VIR.Deep2.router2_fusion_deep
#print axioms VIR.Deep2.router2_fusion_deep_steps
#print VIR.Z.router2z_fusion
#print VIR.Z.slice_fuse_dep
#print VIR.Z.SliceZ.congr_heq_dep
#print VIR.Z.aux_advance_idx
#print axioms VIR.Z.router2z_fusion
#print VIR.Z.SliceZ.heq_of
#print VIR.Z.SliceZ.adv_adv_heq
