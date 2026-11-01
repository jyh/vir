/-
  B′, the Lean mirror (PREDICTIONS-amend-10). Program 3 (inputs/program3-inputs.md K1–K4): A.1's safety theorem over F2.
  ValidFrame is the subtype of the wire, as the MetaPRL arm's vir3.ml defines `validframe` as a set type over `wirebuf`.
  Nothing joins the uninterpreted part: C4vir stays 10.
-/
import VIRB.BPrime2

namespace VIR.BPrime

variable (C : Carrier2)

def whole_slice (b : WireBuf) : VSlice := (b, 0)
def ValidFrame : Type := { b : WireBuf // vlen (whole_slice b) ≥ 24 ∧ read_u32 C.toCarrier (whole_slice b) 0 id = MAGIC }
def frame_sender (b : WireBuf) : Int := read_u32 C.toCarrier (whole_slice b) 4 id
def frame_topic (b : WireBuf) : Int := read_u32 C.toCarrier (whole_slice b) 8 id
def isrouted : Out C.toCarrier → Bool
  | .inl _ => true
  | .inr _ => false

/-- K3 under B′ (E10: the principal is the frame's sender). The premises are the frame, the state and the routed
    premise, as in the MetaPRL arm's three. There is no typing premise. -/
theorem route_acl_safe_bp (b : ValidFrame C) (st : C.State) :
    isrouted C (F2 C (whole_slice b.val) st) = true → C.can_access (frame_sender C b.val) (frame_topic C b.val) = true := by
  intro h
  unfold F2 at h
  simp only [vguard, read_u32, let_lin] at h
  split at h
  · split at h
    · next hc => simp only [Bool.and_eq_true] at hc; exact hc.2.1
    · simp [vdrop, isrouted] at h
  · simp [vdrop, isrouted] at h

end VIR.BPrime
