/-
  O95 VIR program, Lean arm: amend-11 V5 at the ABSTRACT side (STATUS-vir row 78). The five exit witnesses of
  compose/Compose/Drops.lean, rebuilt as abstract stores from the SAME bytes (sender 0, topic 0): the frame's length and
  magic, the ACL bit for (0, 0), and sender 0's tokens. Each theorem states the label ⟦F⟧ gives. The x86 runs exit at
  0x1040 (truncated) · 0x1041 (unauthorised: magic or ACL) · 0x1042 (rate-limited) · the emit. The VIR has ONE code for the
  last three drops (ERR_UNAUTHORIZED_OR_RATE_LIMITED), so the machine's exits are FINER than the VIR's labels. The mapping
  0x1040 ↦ truncated, 0x1041/0x1042 ↦ unauthOrRate, emit ↦ emit 24 is what "agree label by label" means here.
  The relation-based reading (R relates these stores to the machine states) is paris's half, and V4 waits on it.
-/
import VIRP.Router

namespace VIRP

/-- A frame of `n` bytes: the 4 magic bytes (little-endian), then zeros (sender 0, topic 0). -/
def frame (magic : List Int) (n : Nat) : List Int := magic ++ List.replicate (n - 4) 0
def magicLE : List Int := [0x31, 0x47, 0x53, 0x4D]      -- MAGIC = 0x4D534731
def badMagicLE : List Int := [0x00, 0x47, 0x53, 0x4D]   -- Drops.lean's badMagicBuf

def store (w : List Int) (aclBit : Bool) (tokens : Nat) : Store :=
  { wire := w, bucket := fun _ => tokens, acl := fun _ _ => aclBit }

theorem exit_truncated : denote F env0 (store (frame magicLE 10) true 5)
    = Part.some (store (frame magicLE 10) true 5, .drop .truncated) := by
  rw [F_closed]; simp [store, frame, magicLE]

theorem exit_unauth_magic : denote F env0 (store (frame badMagicLE 100) true 5)
    = Part.some (store (frame badMagicLE 100) true 5, .drop .unauthOrRate) := by
  rw [F_closed]; simp [store, frame, badMagicLE, rd32, MAGIC]

theorem exit_unauth_acl : denote F env0 (store (frame magicLE 100) false 5)
    = Part.some (store (frame magicLE 100) false 5, .drop .unauthOrRate) := by
  rw [F_closed]; simp [store, frame, magicLE, rd32, MAGIC]

theorem exit_rate : denote F env0 (store (frame magicLE 100) true 0)
    = Part.some (store (frame magicLE 100) true 0, .drop .unauthOrRate) := by
  rw [F_closed]; simp [store, frame, magicLE, rd32, MAGIC]

theorem exit_emit : denote F env0 (store (frame magicLE 100) true 5)
    = Part.some ((store (frame magicLE 100) true 5).dec 0, .emit 24) := by
  rw [F_closed]; simp [store, frame, magicLE, rd32, MAGIC]

end VIRP
