/-
  PROGRAM 3 (inputs/program3-inputs.md K1-K4; predictions/PREDICTIONS-program3.md, both pinned at vir 98d9329 before
  this file existed): the A.1 safety theorem over program 2's F2, in A.1's idiom (ValidFrame a subtype of the wire buffer).
-/
import VIR.Router2

namespace VIR

/-- A.1's wire buffer and its total accessor (exact on a ValidFrame): the u32 at `i` of the whole buffer. -/
abbrev WireBuf := ByteArray
def wholeSlice (b : WireBuf) : Slice b.size := ⟨b, 0, by simp⟩
def wireRd (b : WireBuf) (i : Nat) : UInt32 := (wholeSlice b).rd i

/-- K2: A.1's ValidFrame, a Prop-carrying subtype. -/
def ValidFrame := { b : WireBuf // 24 ≤ b.size ∧ wireRd b 0 = MAGIC }
def frameSender (b : ValidFrame) : Principal := wireRd b.val 4
def frameTopic (b : ValidFrame) : TopicId := wireRd b.val 8

/-- K3: a return, not a drop. -/
def IsRouted : Out → Prop
  | .ret .. => True
  | .drop _ => False

variable (acl : Principal → TopicId → Bool)

/-- K3, the SCORED theorem of program 3 (E10: the principal is the frame's sender). -/
theorem route_acl_safe (b : ValidFrame) (st : State) :
    IsRouted (F2 acl (wholeSlice b.val) st) → canAccess acl (frameSender b) (frameTopic b) := by
  intro h
  unfold F2 at h
  simp only [guard, readU32, letLin] at h
  split at h
  · split at h
    · next hc => exact hc.2.1
    · exact h.elim
  · exact h.elim

/-- amend-9 (row 25), the L-FLAT control: ValidFrame as a HYPOTHESIS on a bare buffer, cleared before the proof (F2). -/
theorem route_acl_safe_flat (b : WireBuf) (hv : 24 ≤ b.size ∧ wireRd b 0 = MAGIC) (st : State) :
    IsRouted (F2 acl (wholeSlice b) st) → canAccess acl (wireRd b 4) (wireRd b 8) := by
  clear hv
  intro h
  unfold F2 at h
  simp only [guard, readU32, letLin] at h
  split at h
  · split at h
    · next hc => exact hc.2.1
    · exact h.elim
  · exact h.elim

end VIR
