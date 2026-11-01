/-
  STATUS-vir row 39 (O95). One concrete state per DROP outcome, each discharging every hypothesis of
  `lowered_refines_U` (Compose.Lowered), plus a `decide` control on the same state naming its exit and showing
  memory unchanged. Placement as `wState`: rdi 0x10000, rdx 2^48 (paris's 0x8000 violates `hdisj`, RESULTS-3 add. 10).
-/
import Compose.Lowered

namespace VIR.Compose
open X86 Router Router.Refines

/-- A start state with the given length, magic, ACL byte for sender 0 and sender 0's bucket. -/
def mk (len magic aclb tokens : BitVec 64) : Cpu :=
  let c : Cpu := { rip := 0x1000, oracle := Oracle.zero }
  let c := c.setReg .q .rdi 0x10000
  let c := c.setReg .q .rsi len
  let c := c.setReg .q .rdx wRdx
  let c := c.writeMem .d 0x10000 magic
  let c := c.writeMem .d 0x10004 0
  let c := c.writeMem .d 0x10008 0
  let c := c.writeMem .b accl aclb
  c.writeMem .d (wRdx + bucketDisp) tokens

def aclOf (s : Cpu) (p t : UInt32) : Bool :=
  (s.mem.read (0x301d + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8))).getLsbD (t.toNat % 8)
def sigOf (s : Cpu) (p : UInt32) : Int := Value.sval .d (s.mem.readSize .d (Refines.cell (s.regs.get .rdx) p))

theorem aclOf_rel (s : Cpu) : AclRel (aclOf s) s.mem := by intro p t _; rfl
theorem sigOf_rel (s : Cpu) : StRel (sigOf s) s.mem (s.regs.get .rdx) := by intro p; rfl

/-- Disjointness holds for ANY state with rdi 0x10000, rdx 2^48 and len ≤ 100. -/
theorem disj_of (s : Cpu) (hdi : s.regs.get .rdi = 0x10000) (hdx : s.regs.get .rdx = wRdx) (len : Nat)
    (hl : len ≤ 100) : ∀ q : UInt32, ∀ i, i < len →
      ¬ Region (Refines.cell (s.regs.get .rdx) q) 4 (s.regs.get .rdi + BitVec.ofNat 64 i) := by
  rw [hdx, hdi]
  intro q i hi ⟨j, hj, he⟩
  simp only [Refines.cell, wRdx] at he
  bv_omega

def badMagicBuf : ByteArray := ⟨#[0x00, 0x47, 0x53, 0x4D] ++ Array.replicate 96 0⟩

/-! ### TRUNCATED: len 10. -/
def sT := mk 10 Router.MAGIC 1 5
set_option maxRecDepth 200000 in
theorem witness_truncated :
    ∃ n, (runP repaired n sT).stopped = true ∧
      Exit sT (runP repaired n sT) ((VIR.Deep.Val.slice wBuf 0 10).rd 4).toP
        (VIR.Deep.den (aclOf sT) (VIR.Deep.U (.slice wBuf 0 10) (.state (sigOf sT)))) :=
  lowered_refines_U _ sT wBuf 0 10 _ (by decide) (by decide) (by decide)
    (by unfold BufRel; decide) (aclOf_rel sT) (sigOf_rel sT) (by intro h; omega)
    (fun i hi => disj_of sT (by decide) (by decide) 10 (by omega) _ i hi)
set_option maxRecDepth 20000 in
theorem truncated_control : let t := runP repaired 3 sT; t.stopped = true ∧ t.rip = 0x1040 ∧ t.mem.bytes = sT.mem.bytes := by
  decide

/-! ### UNAUTH by magic. -/
def sM := mk 100 0x4D534700 1 5
set_option maxRecDepth 200000 in
theorem witness_unauth_magic :
    ∃ n, (runP repaired n sM).stopped = true ∧
      Exit sM (runP repaired n sM) ((VIR.Deep.Val.slice badMagicBuf 0 100).rd 4).toP
        (VIR.Deep.den (aclOf sM) (VIR.Deep.U (.slice badMagicBuf 0 100) (.state (sigOf sM)))) :=
  lowered_refines_U _ sM badMagicBuf 0 100 _ (by decide) (by decide) (by decide)
    (by unfold BufRel; decide) (aclOf_rel sM) (sigOf_rel sM) (by intro _; decide)
    (fun i hi => disj_of sM (by decide) (by decide) 100 (by omega) _ i hi)
set_option maxRecDepth 20000 in
theorem unauth_magic_control : let t := runP repaired 6 sM; t.stopped = true ∧ t.rip = 0x1041 ∧ t.mem.bytes = sM.mem.bytes := by
  decide

/-! ### UNAUTH by the ACL bit (clear). -/
def sA := mk 100 Router.MAGIC 0 5
set_option maxRecDepth 200000 in
theorem witness_unauth_acl :
    ∃ n, (runP repaired n sA).stopped = true ∧
      Exit sA (runP repaired n sA) ((VIR.Deep.Val.slice wBuf 0 100).rd 4).toP
        (VIR.Deep.den (aclOf sA) (VIR.Deep.U (.slice wBuf 0 100) (.state (sigOf sA)))) :=
  lowered_refines_U _ sA wBuf 0 100 _ (by decide) (by decide) (by decide)
    (by unfold BufRel; decide) (aclOf_rel sA) (sigOf_rel sA) (by intro _; decide)
    (fun i hi => disj_of sA (by decide) (by decide) 100 (by omega) _ i hi)
set_option maxRecDepth 20000 in
theorem unauth_acl_control : let t := runP repaired 11 sA; t.stopped = true ∧ t.rip = 0x1041 ∧ t.mem.bytes = sA.mem.bytes := by
  decide

/-! ### RATE: bucket 0 (the E3 shape; the repaired code leaves the cell unwritten). -/
def sR := mk 100 Router.MAGIC 1 0
set_option maxRecDepth 200000 in
theorem witness_rate :
    ∃ n, (runP repaired n sR).stopped = true ∧
      Exit sR (runP repaired n sR) ((VIR.Deep.Val.slice wBuf 0 100).rd 4).toP
        (VIR.Deep.den (aclOf sR) (VIR.Deep.U (.slice wBuf 0 100) (.state (sigOf sR)))) :=
  lowered_refines_U _ sR wBuf 0 100 _ (by decide) (by decide) (by decide)
    (by unfold BufRel; decide) (aclOf_rel sR) (sigOf_rel sR) (by intro _; decide)
    (fun i hi => disj_of sR (by decide) (by decide) 100 (by omega) _ i hi)
set_option maxRecDepth 20000 in
theorem rate_control : let t := runP repaired 13 sR; t.stopped = true ∧ t.rip = 0x1042 ∧ t.mem.bytes = sR.mem.bytes := by
  decide

/-! ### paris's OWN control layout (`Router.start`, rdx 0x8000) is an instance at d7e992c. -/
def sP := Router.start 100 Router.MAGIC 0 0 1 5
set_option maxRecDepth 200000 in
theorem witness_paris_layout :
    ∃ n, (runP repaired n sP).stopped = true ∧
      Exit sP (runP repaired n sP) ((VIR.Deep.Val.slice wBuf 0 100).rd 4).toP
        (VIR.Deep.den (aclOf sP) (VIR.Deep.U (.slice wBuf 0 100) (.state (sigOf sP)))) := by
  have hdi : sP.regs.get .rdi = 0x10000 := by decide
  have hdx : sP.regs.get .rdx = 0x8000 := by decide
  have hP : ((VIR.Deep.Val.slice wBuf 0 100).rd 4).toP = 0 := by decide
  refine lowered_refines_U _ sP wBuf 0 100 _ (by decide) (by decide) (by decide)
    (by unfold BufRel; decide) (aclOf_rel sP) (sigOf_rel sP) (by intro _; decide) ?_
  have hc : Refines.cell 0x8000 0 = 0xB000 := by decide
  rw [hP, hdx, hdi, hc]
  intro i hi ⟨j, hj, he⟩
  bv_omega

end VIR.Compose
