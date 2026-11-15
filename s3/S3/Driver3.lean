/-
  O95 compiler, the driver at the x86 machine (compiler/DECLARATIONS-DRIVER.md, Addendum 4). Part 1: the fixed loop's code and its
  two paths after the stub returns: a status other than DONE leaves to X; DONE copies the two result words BUF → ENV and jumps back.
-/
import S3.Fragment3
import VIRC.Driver

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

set_option maxHeartbeats 1000000 in
/-- **after_done.** From the stub's DONE return with the two result words at BUF: 10 steps of the loop reach H in AtHead, the next
    call's argument words being those two, the word memory unchanged. -/
theorem after_done {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {X H w0 w1 : W} {wm : WMem} {u : Cpu}
    (hR : Returned L stDone u) (hcm : Common L wm u) (hbuf : WordsAt u.mem L.buf [w0, w1])
    (hc : CodeAt C p u.rip (loopTail L.env0 X H)) (hX : canonical X = true) (hH : canonical H = true) (hN : 2 ≤ L.bufN)
    (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat) :
    ∃ w, runP p 10 u = w ∧ AtHead L H [w0, w1] wm w := by
  obtain ⟨hus, -, hursp, hcb⟩ := hR
  obtain ⟨v, hv, hvs, hvm, hvr, hvrip⟩ := loop_check hus hc hcm hX
  have h0 : rd u.mem L.cb = 0 := hcb
  rw [if_pos h0] at hvrip
  have hsplit : loopTail L.env0 X H = (loopTail L.env0 X H).take 4 ++
      [movi .r12 L.env0, ld .rcx .r14 0, st .r12 0 .rcx, ld .rcx .r14 8, st .r12 8 .rcx, .jmpA H] := rfl
  have hc' : CodeAt C p v.rip [movi .r12 L.env0, ld .rcx .r14 0, st .r12 0 .rcx, ld .rcx .r14 8, st .r12 8 .rcx, .jmpA H] := by
    rw [hvrip]; rw [hsplit] at hc; exact codeAt_right hc
  have hcmv : Common L wm v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hvr .r14 (by decide) (by decide)]; exact hcm.1
    · rw [hvr .rbx (by decide) (by decide)]; exact hcm.2.1
    · rw [hvm]; exact hcm.2.2.1
    · rw [hvm]; exact hcm.2.2.2
  have hbufv : WordsAt v.mem L.buf [w0, w1] := by rw [hvm]; exact hbuf
  have hlo := hL.envlo_le_env0
  obtain ⟨w, hw, hws, hwrip, hwr12, hwr, hwm⟩ := loop_copy hL hvs hc' hH hcmv hbufv hN hlo hE
  have z0 : L.env0 + slot 0 = L.env0 := by simp [slot]
  have z1 : L.env0 + slot 1 = L.env0 + 8 := by simp [slot]
  have ew0 := env_word L (e := L.env0) hlo hE (j := 0) (by decide)
  have ew1 := env_word L (e := L.env0) hlo hE (j := 1) (by decide)
  rw [z0] at ew0; rw [z1] at ew1
  have cbw2 : ∀ k, k < 8 → inCb L (L.cb + 16 + BitVec.ofNat 64 k) := cb_word L (m := 2) (by decide)
  have cbw3 : ∀ k, k < 8 → inCb L (L.cb + 24 + BitVec.ofNat 64 k) := cb_word L (m := 3) (by decide)
  have hT := L.envTop.isLt
  have h8 : (8 : W).toNat = 8 := rfl
  have a01 : VIRBridge.Apart L.env0 (L.env0 + 8) := order_apart (by simp only [BitVec.toNat_add, h8]; omega)
    (by simp only [BitVec.toNat_add, h8]; omega)
  refine ⟨w, by rw [show (10 : Nat) = 4 + 6 from rfl, runP_add, hv, hw], ⟨hws, hwrip, ?_, ?_, hwr12, ?_, ?_, ?_, ?_, ?_, ?_, hstk⟩⟩
  · rw [hwr .r14 (by decide) (by decide), hvr .r14 (by decide) (by decide)]; exact hcm.1
  · rw [hwr .rbx (by decide) (by decide), hvr .rbx (by decide) (by decide)]; exact hcm.2.1
  · rw [hwr .rsp (by decide) (by decide), hvr .rsp (by decide) (by decide)]; exact hursp
  · rw [hwm, rd_write_apart _ _ _ _ (apart_of_disjoint hL.env_cb ew1 cbw2),
      rd_write_apart _ _ _ _ (apart_of_disjoint hL.env_cb ew0 cbw2), hvm]; exact hcm.2.2.1.2.1
  · rw [hwm, rd_write_apart _ _ _ _ (apart_of_disjoint hL.env_cb ew1 cbw3),
      rd_write_apart _ _ _ _ (apart_of_disjoint hL.env_cb ew0 cbw3), hvm]; exact hcm.2.2.1.2.2
  · intro a ha
    have e1 := rd_write_apart (v.mem.writeSize .q L.env0 w0) (L.env0 + 8) a w1
      (apart_of_disjoint hL.env_live ew1 (live_word L ha))
    have e2 := rd_write_apart v.mem L.env0 a w0 (apart_of_disjoint hL.env_live ew0 (live_word L ha))
    simp only [rd] at e1 e2
    rw [hwm, e1, e2, hvm]; exact hcm.2.2.2 a ha
  · intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rw [hwm]
    match j, hj with
    | 0, _ =>
      have e1 := rd_write_apart (v.mem.writeSize .q L.env0 w0) (L.env0 + 8) L.env0 w1 a01.symm'
      simp only [rd] at e1
      have z : L.env0 + BitVec.ofNat 64 (8 * 0) = L.env0 := by simp
      show Mem.readN _ (L.env0 + BitVec.ofNat 64 (8 * 0)) 8 = w0
      rw [z, e1]; exact rd_write_same _ _ _
    | 1, _ =>
      show Mem.readN _ (L.env0 + BitVec.ofNat 64 (8 * 1)) 8 = w1
      rw [show (BitVec.ofNat 64 (8 * 1) : W) = 8 from rfl]; exact rd_write_same _ _ _
  · simpa using hE

/-- **after_exit.** From the stub's return with a status other than DONE: 4 loop steps reach X with that status in the block. -/
theorem after_exit {C : Ctx3} {p : Program} {L : Lay3} {X H code : W} {wm : WMem} {u : Cpu}
    (hR : Returned L code u) (hcm : Common L wm u) (hc : CodeAt C p u.rip (loopTail L.env0 X H)) (hX : canonical X = true)
    (hne : code ≠ 0) : ∃ v, runP p 4 u = v ∧ v.stopped = false ∧ v.rip = X ∧ rd v.mem L.cb = code := by
  obtain ⟨hus, -, -, hcb⟩ := hR
  obtain ⟨v, hv, hvs, hvm, -, hvrip⟩ := loop_check hus hc hcm hX
  rw [if_neg (by rw [hcb]; exact hne)] at hvrip
  exact ⟨v, hv, hvs, hvrip, by rw [hvm]; exact hcb⟩

set_option maxHeartbeats 1000000 in
open VIRL1 VIRL2 in
/-- **drv_iter, one driver iteration.** A ⟶₂ run of a step-shaped e from σ returning its capability, at a store related to the
    machine at the loop head: the machine reaches the head again with the returned words as the next arguments (related at σ₁),
    or leaves the loop at X with a status other than DONE. -/
theorem drv_iter (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) {p : Int} {σ σ₁ : Store}
    (hs : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ) (.ret (.const (.cap p)), σ₁))
    {lay : Int → W} {m : WMem} {ρw : List W}
    (he : EnvRel (lower2T [tcap] e []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw)
    (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] e []).2 (lower2T [tcap] e []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) {s : Cpu} (hA : AtHead L H ρw m s) :
    ∃ n, (∃ ρw' m', AtHead L H ρw' m' (runP P n s) ∧
        EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw' ∧
        Layout σ₁ lay ∧ MemRel lay σ₁ m') ∨
      (∃ code, code ≠ 0 ∧ (runP P n s).rip = X ∧ (runP P n s).stopped = false ∧ rd (runP P n s).mem L.cb = code) := by
  obtain ⟨hDC, hrip1⟩ := head_call hL hA (by rw [hA.rip]; exact hcode) hbase hret
  have h0 := s2_init [tcap] [true] e tcap ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw hty hw hf hok he hl hm
  have hcT : CodeAt C P L.ret0 (loopTail L.env0 X H) := by
    have h1 : CodeAt C P H (.callA base :: loopTail L.env0 X H) := hcode
    have h2 := codeAt_tail h1
    simp only [AI.size] at h2
    rw [hret]; exact h2
  have r1 : ∀ k, runP P (1 + k) s = runP P k (stepP P s) := fun k => by rw [Nat.add_comm]; rfl
  rcases compile_refines_mem [tcap] [true] e tcap [.const (.cap p)] ρw hty hw hf hok rfl (good_cap1 p) hT he hl hm
      _ σ₁ _ hs rfl with ⟨k, ws, m₁, hWN, hv, hl₁, hm₁⟩ | ⟨k, W', hWN, hov⟩
  · have he₁ : EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ws := by
      have := EnvRel.cons (ρw := []) hv .nil
      simpa using this
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j, -, -, -, hres, hcmr⟩⟩ :=
      s3_refines_from_s2 hCdef hP hC hb hT hNm hNt hL hcanon hretc hstub hDC hrip1 h0 hlive hWN
    · obtain ⟨hRet, hcm, -, hbuf⟩ := hR3
      cases hv with
      | cap hRp =>
        obtain ⟨w, hw', hAt⟩ := after_done hL hRet hcm hbuf (by rw [hRet.2.1]; exact hcT) hX hH hN hE hA.stk
        exact ⟨1 + mm + 10, .inl ⟨_, m₁, by rw [runP_add, r1, hw']; exact hAt, he₁, hl₁, hm₁⟩⟩
    · obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hres hcmr (by rw [hres.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stRes, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩
  · obtain ⟨st, m'⟩ := W'
    simp only at hov; subst hov
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j, -, -, -, hres, hcmr⟩⟩ :=
      s3_refines_from_s2 hCdef hP hC hb hT hNm hNt hL hcanon hretc hstub hDC hrip1 h0 hlive hWN
    · obtain ⟨hRet, hcm⟩ := hR3
      obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hRet hcm (by rw [hRet.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stOvf, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩
    · obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hres hcmr (by rw [hres.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stRes, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩

end S3
