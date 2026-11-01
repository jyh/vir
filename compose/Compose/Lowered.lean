/-
  STATUS-vir row 37 (O95). Two vir-side readings of paris's `repaired_refines` (spike 2c0b059), BUILT:
  (a) `lowered_refines_U`: the machine refines the UNFUSED spec composition U, as one term (step 3 + vir's U_exit);
  (b) `witness_*`: a concrete start state satisfying EVERY hypothesis of the theorem, so it is not vacuous.
  ⚠️ At spike 2c0b059 `hdisj` excluded EVERY sender's cell, and paris's control state (`Router.start`, rdx 0x8000) failed it
  (mutant red, RESULTS-3 add. 10). Paris narrowed it to the CURRENT sender's cell at d7e992c (this project re-pinned).
  `w_disj` keeps the old, wide form (it implies the new one); `witness_paris_layout` (Drops.lean) is Router.start itself.
-/
import Router.Refines

namespace VIR.Compose
open X86 Router Router.Refines

theorem den_U_eq_F (acl : VIR.Principal → VIR.TopicId → Bool) (b st : VIR.Deep.Val) :
    VIR.Deep.den acl (VIR.Deep.U b st) = VIR.Deep.den acl (VIR.Deep.F b st) :=
  (VIR.Deep.U_exit acl b st).trans (VIR.Deep.F_exit acl b st).symm

/-- (a) The lowered router refines the spec COMPOSITION U (before fusion), for every state, under I6. -/
theorem lowered_refines_U (acl : VIR.Principal → VIR.TopicId → Bool) (s : Cpu)
    (buf : ByteArray) (off len : Nat) (σ : VIR.State)
    (h : Live s) (hrip : s.rip = 0x1000)
    (hlen : len = (s.regs.get .rsi).toNat)
    (hbuf : BufRel buf off len s.mem (s.regs.get .rdi))
    (hacl : AclRel acl s.mem)
    (hst : StRel σ s.mem (s.regs.get .rdx))
    (htopic : 24 ≤ len → ((VIR.Deep.Val.slice buf off len).rd 8).toP.toNat < 64)
    (hdisj : ∀ i, i < len → ¬ Region (cell (s.regs.get .rdx) ((VIR.Deep.Val.slice buf off len).rd 4).toP) 4
      (s.regs.get .rdi + BitVec.ofNat 64 i)) :
    ∃ n, (runP repaired n s).stopped = true ∧
      Exit s (runP repaired n s) ((VIR.Deep.Val.slice buf off len).rd 4).toP
        (VIR.Deep.den acl (VIR.Deep.U (.slice buf off len) (.state σ))) := by
  rw [den_U_eq_F]
  exact repaired_refines acl s buf off len σ h hrip hlen hbuf hacl hst htopic hdisj

/-! ## (b) Non-vacuity: one concrete state that discharges every hypothesis. -/

def wRdx : BitVec 64 := 0x1000000000000   -- 2^48: the bucket span sits far above the buffer
def wState : Cpu :=
  let c : Cpu := { rip := 0x1000, oracle := Oracle.zero }
  let c := c.setReg .q .rdi 0x10000
  let c := c.setReg .q .rsi 100
  let c := c.setReg .q .rdx wRdx
  let c := c.writeMem .d 0x10000 Router.MAGIC
  let c := c.writeMem .d 0x10004 0
  let c := c.writeMem .d 0x10008 0
  let c := c.writeMem .b accl 1
  c.writeMem .d (wRdx + bucketDisp) 5

/-- The buffer, as the bytes the machine holds at rdi (magic LE, sender 0, topic 0, then zeros). -/
def wBuf : ByteArray := ⟨#[0x31, 0x47, 0x53, 0x4D] ++ Array.replicate 96 0⟩
def wAcl (p t : UInt32) : Bool :=
  (wState.mem.read (0x301d + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8))).getLsbD (t.toNat % 8)
def wSigma (p : UInt32) : Int := Value.sval .d (wState.mem.readSize .d (Refines.cell wRdx p))

set_option maxRecDepth 20000 in
theorem w_live : Live wState := by decide
set_option maxRecDepth 20000 in
theorem w_rip : wState.rip = 0x1000 := by decide
set_option maxRecDepth 20000 in
theorem w_len : (100 : Nat) = (wState.regs.get .rsi).toNat := by decide
set_option maxRecDepth 20000 in
theorem w_rdi : wState.regs.get .rdi = 0x10000 := by decide
set_option maxRecDepth 20000 in
theorem w_rdx : wState.regs.get .rdx = wRdx := by decide

set_option maxRecDepth 200000 in
theorem w_buf : BufRel wBuf 0 100 wState.mem (wState.regs.get .rdi) := by
  rw [w_rdi]; unfold BufRel; decide

theorem w_acl : AclRel wAcl wState.mem := by
  intro p t _; rfl

theorem w_st : StRel wSigma wState.mem (wState.regs.get .rdx) := by
  rw [w_rdx]; intro p; rfl

set_option maxRecDepth 20000 in
theorem w_topic : 24 ≤ 100 → ((VIR.Deep.Val.slice wBuf 0 100).rd 8).toP.toNat < 64 := by
  intro _; decide

theorem w_disj : ∀ q : UInt32, ∀ i, i < 100 →
    ¬ Region (cell (wState.regs.get .rdx) q) 4 (wState.regs.get .rdi + BitVec.ofNat 64 i) := by
  rw [w_rdx, w_rdi]
  intro q i hi ⟨j, hj, he⟩
  simp only [Refines.cell, wRdx] at he
  bv_omega

/-- (b) The theorem APPLIES: every hypothesis discharged on a concrete state, so it is not vacuous. -/
theorem witness_applies :
    ∃ n, (runP repaired n wState).stopped = true ∧
      Exit wState (runP repaired n wState) ((VIR.Deep.Val.slice wBuf 0 100).rd 4).toP
        (VIR.Deep.den wAcl (VIR.Deep.U (.slice wBuf 0 100) (.state wSigma))) :=
  lowered_refines_U wAcl wState wBuf 0 100 wSigma w_live w_rip w_len w_buf w_acl w_st w_topic
    (fun i hi => w_disj _ i hi)

set_option maxRecDepth 20000 in
/-- Positive control on the SAME state: it really takes the OK path (17 steps to emit_slice, cell 5 → 4). -/
theorem witness_ok_control :
    let t := runP repaired 17 wState
    t.stopped = true ∧ t.rip = 0x1043 ∧ t.readMem .d (wRdx + bucketDisp) = 4 := by decide

end VIR.Compose
