import VIRDeflate.Spec
namespace VIRDeflate
set_option pp.proofs false in
#check @lensLoop.eq_2
example (CL : Code) (total fuel : Nat) (lens : Array Nat) : lensLoop CL total (fuel + 1) lens = lensLoop CL total (fuel + 1) lens := by
  conv => lhs; rw [lensLoop]
  trace_state
  rfl
