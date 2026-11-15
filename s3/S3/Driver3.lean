/-
  O95 compiler, the driver at the x86 machine (compiler/DECLARATIONS-DRIVER.md, Addendum 4). Part 1: the fixed loop's code and its
  two paths after the stub returns: a status other than DONE leaves to X; DONE copies the two result words BUF → ENV and jumps back.
-/
import S3.Fragment3

namespace S3
open VIRC X86

/-- The loop after its call (at ret0 = H + 5): test STATUS, leave on non-DONE, else copy the capability's two words to ENV, loop. -/
def loopTail (env0 X H : W) : List AI :=
  [ld .rax .rbx 0, movi .rcx 0, .op (.bin .cmp .q (.reg .rax) (.reg .rcx)), .jccA .ne X,
   movi .r12 env0, ld .rcx .r14 0, st .r12 0 .rcx, ld .rcx .r14 8, st .r12 8 .rcx, .jmpA H]

/-- The whole loop at H: `call base`, then `loopTail`. -/
def loopCode (base env0 X H : W) : List AI := .callA base :: loopTail env0 X H

/-- The check block's first four steps: STATUS into rax, compare with 0, branch. -/
theorem loop_check {C : Ctx3} {p : Program} {L : Lay3} {wm : WMem} {u : Cpu} {env0 X H : W}
    (hs : u.stopped = false) (hc : CodeAt C p u.rip (loopTail env0 X H)) (hcm : Common L wm u) (hX : canonical X = true) :
    ∃ v, runP p 4 u = v ∧ v.stopped = false ∧ v.mem = u.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → v.regs.get r = u.regs.get r) ∧
      v.rip = (if rd u.mem L.cb = 0 then u.rip + BitVec.ofNat 64 (bytes C (loopTail env0 X H |>.take 4)) else X) := by
  have c0 : CodeAt C p u.rip (ld .rax .rbx 0 :: movi .rcx 0 :: .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .jccA .ne X ::
      (loopTail env0 X H).drop 4) := by simpa [loopTail] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p u
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 := codeAt_next (s' := s1) (by rw [e1]) c0
  have e2 := stepP_movi h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 := codeAt_next (s' := s2) (by rw [e2]) c1
  have e3 := stepP_cmp_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 := codeAt_next (s' := s3) (by rw [e3]) c2
  have e4 := stepP_jccA h3 c3 hX
  have hrbx : u.regs.get .rbx = L.cb := hcm.2.1
  have rax2 : s2.regs.get .rax = rd u.mem L.cb := by
    rw [e2, e1]
    simp only [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rax by decide), Regs.get_set_same, hrbx]
    simp
  have rcx2 : s2.regs.get .rcx = 0 := by rw [e2]; simp
  have hne : Cc.eval .ne s3.flags = !decide (rd u.mem L.cb = 0) := by
    rw [e3, rax2, rcx2, cc_ne_sub]
  refine ⟨stepP p s3, rfl, by rw [e4]; exact h3, by rw [e4, e3, e2, e1], ?_, ?_⟩
  · intro r ha hc'; rw [e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  · rw [e4, hne]
    by_cases h0 : rd u.mem L.cb = 0
    · rw [if_pos h0]
      simp only [h0, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [e3, e2, e1]
      simp only [nxt, loopTail, ld, movi, List.take, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl
    · rw [if_neg h0]; simp only [Bool.not_eq_true', decide_eq_false_iff_not, h0, not_false_eq_true, if_true]

set_option maxHeartbeats 1000000 in
/-- The copy block (DONE path): r12 := env0, the capability's two words BUF → ENV, jump to H. 6 steps. -/
theorem loop_copy {C : Ctx3} {p : Program} {L : Lay3} {wm : WMem} {v : Cpu} {env0 H w0 w1 : W} (hL : L.Ok)
    (hs : v.stopped = false)
    (hc : CodeAt C p v.rip [movi .r12 env0, ld .rcx .r14 0, st .r12 0 .rcx, ld .rcx .r14 8, st .r12 8 .rcx, .jmpA H])
    (hH : canonical H = true) (hcm : Common L wm v) (hbuf : WordsAt v.mem L.buf [w0, w1]) (hN : 2 ≤ L.bufN)
    (hlo : L.envLo.toNat ≤ env0.toNat) (hhi : env0.toNat + 8 * 2 ≤ L.envTop.toNat) :
    ∃ u, runP p 6 v = u ∧ u.stopped = false ∧ u.rip = H ∧ u.regs.get .r12 = env0 ∧
      (∀ r, r ≠ .rcx → r ≠ .r12 → u.regs.get r = v.regs.get r) ∧
      u.mem = (v.mem.writeSize .q env0 w0).writeSize .q (env0 + 8) w1 := by
  have e1 := stepP_movi hs hc
  set s1 := stepP p v
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 := codeAt_next (s' := s1) (by rw [e1]) hc
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 := codeAt_next (s' := s2) (by rw [e2]) c1
  have e3 := stepP_st h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 := codeAt_next (s' := s3) (by rw [e3]) c2
  have e4 := stepP_ld h3 c3
  set s4 := stepP p s3
  have h4 : s4.stopped = false := by rw [e4]; exact h3
  have c4 := codeAt_next (s' := s4) (by rw [e4]) c3
  have e5 := stepP_st h4 c4
  set s5 := stepP p s4
  have h5 : s5.stopped = false := by rw [e5]; exact h4
  have c5 := codeAt_next (s' := s5) (by rw [e5]) c4
  have e6 := stepP_jmpA h5 c5 hH
  have hB : v.regs.get .r14 = L.buf := hcm.1
  have zb : L.buf + (0 : W) = L.buf := by simp
  have ze : env0 + (0 : W) = env0 := by simp
  have r12_1 : s1.regs.get .r12 = env0 := by rw [e1]; dsimp only; exact Regs.get_set_same _ _ _
  have r14_1 : s1.regs.get .r14 = L.buf := by
    rw [e1]; dsimp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.r14 by decide), hB]
  have w0eq : rd v.mem L.buf = w0 := by
    have := hbuf 0 (by simp); simpa [rd] using this
  have rcx2 : s2.regs.get .rcx = w0 := by
    rw [e2]; dsimp only; rw [Regs.get_set_same, r14_1, zb, show s1.mem = v.mem by rw [e1]]; exact w0eq
  have r12_2 : s2.regs.get .r12 = env0 := by
    rw [e2]; dsimp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.r12 by decide)]; exact r12_1
  have r14_2 : s2.regs.get .r14 = L.buf := by
    rw [e2]; dsimp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.r14 by decide)]; exact r14_1
  have mem3 : s3.mem = v.mem.writeSize .q env0 w0 := by
    rw [e3]; dsimp only; rw [r12_2, rcx2, ze, show s2.mem = v.mem by rw [e2, e1]]
  have ap1 : VIRBridge.Apart env0 (L.buf + slot 1) := by
    have := buf_env_apart hL (i := 1) (by omega) hlo hhi (j := 0) (by decide)
    simpa [slot] using this.symm'
  have w1eq : rd s3.mem (L.buf + 8) = w1 := by
    rw [mem3]
    have := rd_write_apart v.mem env0 (L.buf + slot 1) w0 ap1
    simp only [slot] at this
    rw [show (BitVec.ofNat 64 (8 * 1) : W) = 8 from rfl] at this
    rw [this]
    have := hbuf 1 (by simp); simpa [rd] using this
  have r14_3 : s3.regs.get .r14 = L.buf := by rw [e3]; exact r14_2
  have r12_3 : s3.regs.get .r12 = env0 := by rw [e3]; exact r12_2
  have rcx4 : s4.regs.get .rcx = w1 := by
    rw [e4]; dsimp only; rw [Regs.get_set_same, r14_3]; exact w1eq
  have r12_4 : s4.regs.get .r12 = env0 := by
    rw [e4]; dsimp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.r12 by decide)]; exact r12_3
  have mem5 : s5.mem = (v.mem.writeSize .q env0 w0).writeSize .q (env0 + 8) w1 := by
    rw [e5, r12_4, rcx4, show s4.mem = s3.mem by rw [e4], mem3]
  refine ⟨stepP p s5, rfl, by rw [e6]; exact h5, by rw [e6], ?_, ?_, by rw [e6]; exact mem5⟩
  · rw [e6, e5]; exact r12_4
  · intro r hr1 hr2
    rw [e6, e5, e4, e3, e2, e1]; dsimp only
    rw [Regs.get_set_ne _ _ _ _ (Ne.symm hr1), Regs.get_set_ne _ _ _ _ (Ne.symm hr1), Regs.get_set_ne _ _ _ _ (Ne.symm hr2)]

/-- The loop head's invariant: at H, the registers the stub expects except the pushed return address, the control block's ENV/STACK
    bounds, the word memory represented on L.live, and the next call's argument words at env0. -/
structure AtHead (L : Lay3) (H : W) (ρ : List W) (wm : WMem) (s : Cpu) : Prop where
  stopped : s.stopped = false
  rip : s.rip = H
  r14 : s.regs.get .r14 = L.buf
  rbx : s.regs.get .rbx = L.cb
  r12 : s.regs.get .r12 = L.env0
  rsp : s.regs.get .rsp = L.rsp0 + 8
  cb16 : rd s.mem (L.cb + 16) = L.envLo
  cb24 : rd s.mem (L.cb + 24) = L.stkLo
  rep : VIRBridge.Rep wm s.mem L.live
  words : WordsAt s.mem L.env0 ρ
  hi : L.env0.toNat + 8 * ρ.length ≤ L.envTop.toNat
  stk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat

/-- **head_call.** The loop's `call base` from AtHead lands at base in DriverCall (it pushes ret0 = H + 5 at rsp0). -/
theorem head_call {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {H base : W} {ρ : List W} {wm : WMem} {s : Cpu}
    {l : List AI} (hA : AtHead L H ρ wm s) (hc : CodeAt C p s.rip (.callA base :: l)) (hbase : canonical base = true)
    (hret : L.ret0 = H + 5) : DriverCall L ρ wm (stepP p s) ∧ (stepP p s).rip = base := by
  have e := stepP_callA hA.stopped hc hbase
  have hsp : s.regs.get .rsp - 8 = L.rsp0 := by rw [hA.rsp]; exact BitVec.add_sub_cancel _ _
  have stkw : ∀ k, k < 8 → inStk L (L.rsp0 + BitVec.ofNat 64 k) :=
    stk_word L (x := L.rsp0) (by have := hL.stk_lo_le; omega) (le_refl _) hL
  have cbw2 : ∀ k, k < 8 → inCb L (L.cb + 16 + BitVec.ofNat 64 k) := cb_word L (m := 2) (by decide)
  have cbw3 : ∀ k, k < 8 → inCb L (L.cb + 24 + BitVec.ofNat 64 k) := cb_word L (m := 3) (by decide)
  have a2 : VIRBridge.Apart L.rsp0 (L.cb + 16) := apart_of_disjoint hL.stk_cb stkw cbw2
  have a3 : VIRBridge.Apart L.rsp0 (L.cb + 24) := apart_of_disjoint hL.stk_cb stkw cbw3
  rw [e]
  refine ⟨⟨hA.stopped, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA.hi, hA.stk⟩, rfl⟩
  · dsimp only; rw [Regs.get_set_ne _ _ _ _ (by decide : GPR.rsp ≠ GPR.r14)]; exact hA.r14
  · dsimp only; rw [Regs.get_set_ne _ _ _ _ (by decide : GPR.rsp ≠ GPR.rbx)]; exact hA.rbx
  · dsimp only; rw [Regs.get_set_ne _ _ _ _ (by decide : GPR.rsp ≠ GPR.r12)]; exact hA.r12
  · dsimp only; rw [Regs.get_set_same]; exact hsp
  · dsimp only; rw [hsp, rd_write_same, hA.rip, hret]
  · dsimp only; rw [hsp, rd_write_apart _ _ _ _ a2]; exact hA.cb16
  · dsimp only; rw [hsp, rd_write_apart _ _ _ _ a3]; exact hA.cb24
  · dsimp only; rw [hsp]
    intro a ha
    have := rd_write_apart s.mem L.rsp0 a (s.rip + 5) (apart_of_disjoint hL.stk_live stkw (live_word L ha))
    simp only [rd] at this; rw [this]; exact hA.rep a ha
  · dsimp only; rw [hsp]
    refine wordsAt_write_apart (fun j hj => ?_) hA.words
    exact apart_of_disjoint (fun a h1 h2 => hL.env_stk a h2 h1) stkw
      (env_word L (e := L.env0) hL.envlo_le_env0 hA.hi hj)

end S3
