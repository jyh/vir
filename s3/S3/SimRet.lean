/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 9): the word step `ret o`. A return to the entry stub (k = []) reaches
  the driver as R3 `done`; a return into a pending frame runs the runtime prepend (Addendum 1's loop over r13) and reaches the
  continuation as an R3 run state at `ws ++ ρ₂`, or RES with the successor state outgrowing ENV (`RetOver`, Addendum 9).
  A separate module beside Sim3, which it imports and does not edit.
-/
import S3.Sim3

namespace S3
open VIRC X86

/-! ## Fetch-and-step for the forms a return uses -/

theorem stepP_pop {C : Ctx3} {p : Program} {s : Cpu} {r : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.pop .q (.reg r)) :: l)) (hr : GPR.rsp ≠ r) :
    stepP p s = { s with regs := (s.regs.set .rsp (s.regs.get .rsp + 8)).set r (rd s.mem (s.regs.get .rsp)), rip := nxt C s.rip (.op (.pop .q (.reg r))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_pop_reg .q r (live_of hs) hr]
  simp [Value.writeView, Mem.readSize, Size.bytes, rd, nxt, AI.size]

theorem stepP_jmpA {C : Ctx3} {p : Program} {s : Cpu} {a : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.jmpA a :: l)) (hcan : canonical a = true) :
    stepP p s = { s with rip := a } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  have e : s.rip + BitVec.ofNat 64 5 + (a - (s.rip + 5)) = a := by bv_omega
  rw [step_jmp_rel _ (live_of hs) (by have h := hcan; rw [← e] at h; exact h)]
  simp [add_sub_self']

theorem stepP_lea_sc {C : Ctx3} {p : Program} {s : Cpu} {d i : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.lea .q d { index := some i, scale := .s8 }) :: l)) :
    stepP p s = { s with regs := s.regs.set d (s.regs.get i * 8), rip := nxt C s.rip (.op (.lea .q d { index := some i, scale := .s8 })) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_lea .q d _ (live_of hs) rfl]
  simp [Value.writeView, Ea.offset, Scale.toVal, nxt, AI.size]

theorem stepP_ld_idx {C : Ctx3} {p : Program} {s : Cpu} {r b i : GPR} {l : List AI}
    (hs : s.stopped = false)
    (hc : CodeAt C p s.rip (.op (.mov .q (.reg r) (.mem { base := some b, index := some i, scale := .s8 })) :: l)) :
    stepP p s = { s with regs := s.regs.set r (rd s.mem (s.regs.get b + s.regs.get i * 8)), rip := nxt C s.rip (.op (.mov .q (.reg r) (.mem { base := some b, index := some i, scale := .s8 }))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_mov_reg_mem .q r _ (live_of hs) rfl]
  simp [Ea.offset, Scale.toVal, Value.writeView, Mem.readSize, Size.bytes, rd, nxt, AI.size]

theorem stepP_st_idx {C : Ctx3} {p : Program} {s : Cpu} {r b i : GPR} {l : List AI}
    (hs : s.stopped = false)
    (hc : CodeAt C p s.rip (.op (.mov .q (.mem { base := some b, index := some i, scale := .s8 }) (.reg r)) :: l)) :
    stepP p s = { s with mem := s.mem.writeSize .q (s.regs.get b + s.regs.get i * 8) (s.regs.get r), rip := nxt C s.rip (.op (.mov .q (.mem { base := some b, index := some i, scale := .s8 }) (.reg r))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_mov_mem_reg .q _ r (live_of hs) rfl]
  simp [Ea.offset, Scale.toVal, Cpu.getReg, nxt, AI.size]

theorem stepP_add_ri1 {C : Ctx3} {p : Program} {s : Cpu} {r : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .add .q (.reg r) (.imm 1)) :: l)) :
    (stepP p s).regs = s.regs.set r (s.regs.get r + 1) ∧ (stepP p s).mem = s.mem ∧
      (stepP p s).rip = nxt C s.rip (.op (.bin .add .q (.reg r) (.imm 1))) ∧ (stepP p s).stopped = s.stopped := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_add_reg_op .q r false (.imm 1) (live_of hs) rfl]
  simp [Value.writeView, Flags.addResult, Cpu.getReg, Cpu.readOperand, Value.trunc_q, nxt, AI.size, Cpu.stopped]

/-! ## A return to the entry stub -/

/-- The successor word state outgrows ENV (Addendum 9). -/
def RetOver (L : Lay3) : WSt → Prop
  | .run _ ρ k => EnvOver L ρ k 0
  | _ => False

theorem cb_buf_apart {L : Lay3} (hL : L.Ok) {i : Nat} (hi : i < L.bufN) : VIRBridge.Apart L.cb (L.buf + slot i) := by
  have := buf_cb_apart hL hi (m := 0) (by decide)
  simpa using this.symm'

theorem wordsAt_write_apart {m : Mem} {a v B : W} {ws : List W} (hap : ∀ j, j < ws.length → VIRBridge.Apart a (B + slot j))
    (hw : WordsAt m B ws) : WordsAt (m.writeSize .q a v) B ws := by
  intro j hj
  have := rd_write_apart m a (B + slot j) v (hap j hj)
  simp only [rd, slot] at this; rw [this]; exact hw j hj

/-- **sim_ret_nil.** `ret o` with no pending frame: the driver sees DONE with the result's words at BUF and their count in r13. -/
theorem sim_ret_nil {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {o : WOpd}
    {ρ : List W} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.ret o) ρ [], wm) s)
    (hneed : need o ≤ L.bufN) {W' : WSt × WMem} (hstep : stepW tbl (.run (.ret o) ρ [], wm) = some W') :
    ∃ n, 0 < n ∧ R3 C p L W' (runP p n s) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hB : s.regs.get .r14 = L.buf := hcom.1
  have hX : s.regs.get .rbx = L.cb := hcom.2.1
  obtain ⟨_, _, ⟨hc1, hc2, hc3⟩, hRep⟩ := hcom
  have hL := E.ok
  obtain ⟨fq, fcode, fa, frsp, fret, _⟩ := hfr
  have hc : CodeAt C p s.rip (evalTo C 0 o ++ [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret]) := by
    have h0 := hcode; simp only [gen] at h0; exact h0
  have hpre : EvalPre s 0 L.bufN ρ := ⟨hw, by rw [hB]; exact hL.buf_nowrap,
    fun i j _ hi hj => by rw [hB]; exact buf_env_apart hL hi hlo hhi hj⟩
  have hpost := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) o 0 s _ ρ L.bufN hs hc (by omega) hpre
  simp only [EvalPost] at hpost
  simp only [stepW] at hstep
  cases ho : evalW ρ o with
  | bad => rw [ho] at hstep; cases hstep
  | ovf =>
    rw [ho] at hstep hpost; cases hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := hpost
    obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 (agree_of_frame hB hf1) hf1.2 hs1 hrip1
    exact ⟨n1 + 4, by omega, by rw [runP_add, hr1, hv]; exact hRv⟩
  | ok ws =>
    rw [ho] at hstep hpost
    simp only [Option.some.injEq] at hstep; subst hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := hpost
    have hlen : ws.length = wid o := evalW_length o ρ ws ho
    have ag1 : AgreeBuf L s.mem u1.mem := agree_of_frame hB hf1
    have hR := L.rsp0.isLt
    have hst := hL.stk_nowrap
    have hsp := (s.regs.get .rsp).isLt
    set sp := s.regs.get .rsp with hsp_def
    have e8 : (sp + 8).toNat = sp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    have e16 : sp + 8 + 8 = L.rsp0 := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add]; simp; omega
    -- the stack words the return reads are untouched by the operand code
    have m_sp : rd u1.mem sp = L.stubRet := by
      rw [ag1 sp (fun i hi => buf_stk_apart hL hi hsl (by omega))]; exact fq
    have m_sp8 : rd u1.mem (sp + 8) = L.env0 := by
      rw [ag1 (sp + 8) (fun i hi => buf_stk_apart hL hi (by omega) (by omega))]; exact fa
    have m_r0 : rd u1.mem L.rsp0 = L.ret0 := by
      rw [ag1 L.rsp0 (fun i hi => buf_stk_apart hL hi hL.stk_lo_le (le_refl _))]; exact fret
    have c1 : CodeAt C p u1.rip [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret] := by
      rw [hrip1]; exact codeAt_right hc
    have e2 := stepP_movi hs1 c1
    set u2 := stepP p u1 with hu2
    have h2 : u2.stopped = false := by rw [e2]; exact hs1
    have c2 : CodeAt C p u2.rip [.op .ret] := by rw [e2]; exact codeAt_tail c1
    have sp2 : u2.regs.get .rsp = sp := by
      rw [e2]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r13 ≠ GPR.rsp by decide)]
      exact hf1.2 .rsp (by decide) (by decide) (by decide)
    have e3 := stepP_ret h2 c2 (by rw [sp2, show u2.mem = u1.mem by rw [e2], m_sp]; exact canon_of_codeAt E fcode)
    set u3 := stepP p u2 with hu3
    have h3 : u3.stopped = false := by rw [e3]; exact h2
    have mem3 : u3.mem = u1.mem := by rw [e3, e2]
    have rip3 : u3.rip = L.stubRet := by rw [e3]; simp only [sp2, show u2.mem = u1.mem by rw [e2], m_sp]
    have sp3 : u3.regs.get .rsp = sp + 8 := by rw [e3]; simp [sp2]
    have c3 : CodeAt C p u3.rip (.op (.pop .q (.reg .r12)) :: movi .rax stDone :: st .rbx 0 .rax :: .op .ret :: []) := by
      rw [rip3]; exact fcode
    have e4 := stepP_pop h3 c3 (by decide)
    set u4 := stepP p u3 with hu4
    have h4 : u4.stopped = false := by rw [e4]; exact h3
    have c4 : CodeAt C p u4.rip (movi .rax stDone :: st .rbx 0 .rax :: .op .ret :: []) := by rw [e4]; exact codeAt_tail c3
    have sp4 : u4.regs.get .rsp = L.rsp0 := by
      rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rsp by decide), Regs.get_set_same, sp3, e16]
    have e5 := stepP_movi h4 c4
    set u5 := stepP p u4 with hu5
    have h5 : u5.stopped = false := by rw [e5]; exact h4
    have c5 : CodeAt C p u5.rip (st .rbx 0 .rax :: .op .ret :: []) := by rw [e5]; exact codeAt_tail c4
    have rbx4 : u4.regs.get .rbx = L.cb := by
      rw [e4, e3, e2]
      simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rbx by decide), Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.rbx by decide),
        Regs.get_set_ne _ _ _ _ (show GPR.r13 ≠ GPR.rbx by decide)]
      rw [hf1.2 .rbx (by decide) (by decide) (by decide), hX]
    have e6 := stepP_st h5 c5
    set u6 := stepP p u5 with hu6
    have h6 : u6.stopped = false := by rw [e6]; exact h5
    have c6 : CodeAt C p u6.rip (.op .ret :: []) := by rw [e6]; exact codeAt_tail c5
    have mem6 : u6.mem = u1.mem.writeSize .q L.cb stDone := by
      rw [e6, e5]; simp [rbx4, mem3, show u4.mem = u3.mem by rw [e4]]
    have sp6 : u6.regs.get .rsp = L.rsp0 := by rw [e6, e5]; simp [sp4]
    have cbw0 : ∀ k, k < 8 → inCb L (L.cb + BitVec.ofNat 64 k) := fun k hk => ⟨k, by omega, rfl⟩
    have a0s : VIRBridge.Apart L.cb L.rsp0 := apart_of_disjoint (fun a h1 h2 => hL.stk_cb a h2 h1) cbw0 (by
      intro j hj
      have e : (L.rsp0 + BitVec.ofNat 64 j).toNat = L.rsp0.toNat + j := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [inStk, e]; constructor
      · have := hL.stk_lo_le; omega
      · omega)
    have m6r : rd u6.mem L.rsp0 = L.ret0 := by rw [mem6, rd_write_apart _ _ _ _ a0s, m_r0]
    have e7 := stepP_ret h6 c6 (by rw [sp6, m6r]; exact E.ret_canon)
    have hcbN := hL.cb_nowrap
    have a01 : VIRBridge.Apart L.cb (L.cb + 8) := by
      have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 1) (by decide) (by decide) (by decide)
      simpa [slot] using this
    have a02 : VIRBridge.Apart L.cb (L.cb + 16) := by
      have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 2) (by decide) (by decide) (by decide)
      simpa [slot] using this
    have a03 : VIRBridge.Apart L.cb (L.cb + 24) := by
      have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 3) (by decide) (by decide) (by decide)
      simpa [slot] using this
    have reg6 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r12 → r ≠ .rsp → r ≠ .r13 → u6.regs.get r = s.regs.get r := by
      intro r ha hc' hd h12 hsp' h13
      rw [e6, e5, e4, e3, e2]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm h12), Regs.get_set_ne _ _ _ _ (Ne.symm hsp'),
        Regs.get_set_ne _ _ _ _ (Ne.symm h13)]
      exact hf1.2 r ha hc' hd
    refine ⟨n1 + 6, by omega, ?_⟩
    rw [runP_add, hr1]
    show R3 C p L _ (stepP p u6)
    refine ⟨⟨by rw [e7]; exact h6, by rw [e7]; simp only [sp6, m6r], by rw [e7]; simp [sp6], ?_⟩, ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · rw [e7]; simp only; rw [mem6]; exact rd_write_same _ _ _
    · rw [e7]; simp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.r14 by decide), reg6 .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hB]
    · rw [e7]; simp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.rbx by decide), reg6 .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hX]
    · rw [e7]; simp only; rw [mem6, rd_write_apart _ _ _ _ a01, ag1 (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide))]
      exact hc1
    · rw [e7]; simp only; rw [mem6, rd_write_apart _ _ _ _ a02, ag1 (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]
      exact hc2
    · rw [e7]; simp only; rw [mem6, rd_write_apart _ _ _ _ a03, ag1 (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide))]
      exact hc3
    · intro a ha
      rw [e7]; simp only; rw [mem6]
      have h1 := rd_write_apart u1.mem L.cb a stDone (apart_of_disjoint hL.cb_live cbw0 (live_word L ha))
      have h2 := ag1 a (fun i hi => buf_live_apart hL hi ha)
      simp only [rd] at h1 h2; rw [h1, h2]; exact hRep a ha
    · rw [e7]; simp only; rw [Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.r13 by decide)]
      rw [e6, e5, e4, e3, e2]
      simp only [Regs.get_set_ne _ _ _ _ (show GPR.rax ≠ GPR.r13 by decide), Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.r13 by decide),
        Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.r13 by decide), Regs.get_set_same, hlen]
    · rw [e7]; simp only; rw [mem6]
      have hw1' : WordsAt u1.mem L.buf ws := by have := hw1; rw [hB] at this; simpa [slot] using this
      have hlenN : ws.length ≤ L.bufN := by rw [hlen]; exact le_trans (wid_le_need o) hneed
      exact wordsAt_write_apart (fun j hj => cb_buf_apart hL (by omega)) hw1'


/-! ## The runtime prepend (Addendum 1): a loop over r13 -/

theorem codeAt_jcc_fall {C : Ctx3} {p : Program} {s : Cpu} {c : Cc} {a : W} {l : List AI}
    (hc : CodeAt C p s.rip (.jccA c a :: l)) : CodeAt C p (s.rip + 6) l := by
  have h := codeAt_tail hc
  have e : s.rip + BitVec.ofNat 64 (AI.size C (.jccA c a)) = s.rip + 6 := by simp [AI.size]
  rw [e] at h; exact h

def plPre (C : Ctx3) : List AI :=
  [ld .rdx .rbx 16, .op (.mov .q (.reg .rax) (.reg .r12)), .op (.bin .sub .q (.reg .rax) (.reg .rdx)),
   .op (.lea .q .rcx { index := some .r13, scale := .s8 }), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)), .jccA .b C.res,
   .op (.bin .sub .q (.reg .r12) (.reg .rcx)), movi .rcx 0]
def plTest : List AI := [.op (.bin .cmp .q (.reg .rcx) (.reg .r13))]
def plBody : List AI :=
  [.op (.mov .q (.reg .rax) (.mem { base := some .r14, index := some .rcx, scale := .s8 })),
   .op (.mov .q (.mem { base := some .r12, index := some .rcx, scale := .s8 }) (.reg .rax)),
   .op (.bin .add .q (.reg .rcx) (.imm 1))]
def plHead (C : Ctx3) (pc : W) : W := pc + BitVec.ofNat 64 (bytes C (plPre C))
def plExit (C : Ctx3) (pc : W) : W := plHead C pc + BitVec.ofNat 64 (bytes C plTest + 6 + bytes C plBody + 5)

theorem prependLoop_eq (C : Ctx3) (pc : W) :
    prependLoop C pc = plPre C ++ plTest ++ [.jccA .ae (plExit C pc)] ++ plBody ++ [.jmpA (plHead C pc)] := rfl

theorem plExit_eq (C : Ctx3) (pc : W) : plExit C pc = pc + BitVec.ofNat 64 (bytes C (prependLoop C pc)) := by
  rw [prependLoop_eq]
  simp only [plExit, plHead, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]

theorem ofNat_mul8 (i : Nat) : BitVec.ofNat 64 i * 8 = slot i := by
  apply BitVec.eq_of_toNat_eq; simp [slot, BitVec.toNat_mul] <;> omega

/-- **loop_run.** From the loop head with rcx = i ≤ n = r13, the BUF words at B (r14), and words 0..i−1 already copied to e (r12):
    the loop reaches its exit with all n words copied, memory apart from the n new words unchanged, r12/r13/r14 and every register
    but rax, rcx unchanged. -/
theorem loop_run {C : Ctx3} {p : Program} {pc : W} {B e : W} {ws : List W}
    (hcode : CodeAt C p (plHead C pc) (plTest ++ [.jccA .ae (plExit C pc)] ++ plBody ++ [.jmpA (plHead C pc)]))
    (hcx : canonical (plExit C pc) = true) (hch : canonical (plHead C pc) = true)
    (hn64 : 8 * ws.length < 2 ^ 64)
    (hBE : ∀ j j', j < ws.length → j' < ws.length → VIRBridge.Apart (e + slot j) (B + slot j'))
    (hEE : ∀ j j', j < ws.length → j' < ws.length → j ≠ j' → VIRBridge.Apart (e + slot j) (e + slot j')) :
    ∀ d i (v : Cpu), ws.length - i = d → i ≤ ws.length → v.stopped = false → v.rip = plHead C pc →
      v.regs.get .rcx = BitVec.ofNat 64 i → v.regs.get .r13 = BitVec.ofNat 64 ws.length → v.regs.get .r14 = B →
      v.regs.get .r12 = e → (∀ j (h : j < ws.length), rd v.mem (B + slot j) = ws[j]) →
      (∀ j (h : j < i) (h' : j < ws.length), rd v.mem (e + slot j) = ws[j]) →
      ∃ m u, runP p m v = u ∧ u.stopped = false ∧ u.rip = plExit C pc ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = v.regs.get r) ∧
        (∀ j (h : j < ws.length), rd u.mem (e + slot j) = ws[j]) ∧
        (∀ a, (∀ j, j < ws.length → VIRBridge.Apart (e + slot j) a) → rd u.mem a = rd v.mem a) := by
  intro d
  induction d with
  | zero =>
    intro i v hd hi hs hrip hcx' h13 h14 h12 hB hE
    have hin : i = ws.length := by omega
    have c0 : CodeAt C p v.rip (.op (.bin .cmp .q (.reg .rcx) (.reg .r13)) :: .jccA .ae (plExit C pc) :: (plBody ++ [.jmpA (plHead C pc)])) := by
      rw [hrip]; simpa [plTest] using hcode
    have e1 := stepP_cmp_rr hs c0
    set v1 := stepP p v with hv1
    have h1 : v1.stopped = false := by rw [e1]; exact hs
    have c1 : CodeAt C p v1.rip (.jccA .ae (plExit C pc) :: (plBody ++ [.jmpA (plHead C pc)])) := by rw [e1]; exact codeAt_tail c0
    have e2 := stepP_jccA h1 c1 hcx
    have hae : Cc.eval .ae v1.flags = true := by
      rw [e1, cc_ae_of_sub]; simp only [hcx', h13, Value.uval, Value.trunc_q, hin, decide_eq_true_eq, le_refl]
    refine ⟨2, stepP p v1, rfl, by rw [e2]; exact h1, by rw [e2]; simp only [hae, if_true], ?_, ?_, ?_⟩
    · intro r ha hc; rw [e2, e1]
    · intro j hj; rw [e2, e1]; exact hE j (by omega) hj
    · intro a _; rw [e2, e1]
  | succ d ih =>
    intro i v hd hi hs hrip hcx' h13 h14 h12 hB hE
    have hin : i < ws.length := by omega
    have c0 : CodeAt C p v.rip (.op (.bin .cmp .q (.reg .rcx) (.reg .r13)) :: .jccA .ae (plExit C pc) ::
        .op (.mov .q (.reg .rax) (.mem { base := some .r14, index := some .rcx, scale := .s8 })) ::
        .op (.mov .q (.mem { base := some .r12, index := some .rcx, scale := .s8 }) (.reg .rax)) ::
        .op (.bin .add .q (.reg .rcx) (.imm 1)) :: .jmpA (plHead C pc) :: []) := by
      rw [hrip]; simpa [plTest, plBody] using hcode
    have e1 := stepP_cmp_rr hs c0
    set v1 := stepP p v with hv1
    have h1 : v1.stopped = false := by rw [e1]; exact hs
    have c1 := codeAt_next (s' := v1) (by rw [e1]) c0
    have e2 := stepP_jccA h1 c1 hcx
    have hae : Cc.eval .ae v1.flags = false := by
      rw [e1, cc_ae_of_sub]; simp only [hcx', h13, Value.uval, Value.trunc_q, decide_eq_false_iff_not, Nat.not_le,
        BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hin
    set v2 := stepP p v1 with hv2
    have h2 : v2.stopped = false := by rw [e2]; exact h1
    have c2 : CodeAt C p v2.rip (.op (.mov .q (.reg .rax) (.mem { base := some .r14, index := some .rcx, scale := .s8 })) ::
        .op (.mov .q (.mem { base := some .r12, index := some .rcx, scale := .s8 }) (.reg .rax)) ::
        .op (.bin .add .q (.reg .rcx) (.imm 1)) :: .jmpA (plHead C pc) :: []) := by
      rw [e2]; simp only [hae, Bool.false_eq_true, if_false]; exact codeAt_jcc_fall c1
    have e3 := stepP_ld_idx h2 c2
    set v3 := stepP p v2 with hv3
    have h3 : v3.stopped = false := by rw [e3]; exact h2
    have c3 := codeAt_next (s' := v3) (by rw [e3]) c2
    have e4 := stepP_st_idx h3 c3
    set v4 := stepP p v3 with hv4
    have h4 : v4.stopped = false := by rw [e4]; exact h3
    have c4 := codeAt_next (s' := v4) (by rw [e4]) c3
    have e5 := stepP_add_ri1 h4 c4
    set v5 := stepP p v4 with hv5
    have h5 : v5.stopped = false := by rw [e5.2.2.2]; exact h4
    have c5 : CodeAt C p v5.rip (.jmpA (plHead C pc) :: []) := by rw [e5.2.2.1]; exact codeAt_tail c4
    have e6 := stepP_jmpA h5 c5 hch
    set v6 := stepP p v5 with hv6
    -- register facts along the pass
    have r2 : v2.regs = v.regs := by rw [e2, e1]
    have rcx2 : v2.regs.get .rcx = BitVec.ofNat 64 i := by rw [r2]; exact hcx'
    have rax3 : v3.regs.get .rax = ws[i] := by
      rw [e3]; simp only [Regs.get_set_same]
      rw [show v2.mem = v.mem by rw [e2, e1], r2, h14, hcx', ofNat_mul8]; exact hB i hin
    have r3 : ∀ r, r ≠ .rax → v3.regs.get r = v.regs.get r := by
      intro r hr; rw [e3]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hr)]; rw [r2]
    have mem4 : v4.mem = v.mem.writeSize .q (e + slot i) ws[i] := by
      rw [e4]; simp only
      rw [r3 .r12 (by decide), r3 .rcx (by decide), h12, hcx', ofNat_mul8, rax3, show v3.mem = v.mem by rw [e3, e2, e1]]
    have r6 : v6.regs = v4.regs.set .rcx (v4.regs.get .rcx + 1) := by rw [e6]; exact e5.1
    have r4 : v4.regs = v3.regs := by rw [e4]
    have rcx6 : v6.regs.get .rcx = BitVec.ofNat 64 (i + 1) := by
      rw [r6, Regs.get_set_same, r4, r3 .rcx (by decide), hcx', ofNat_add64]; rfl
    have reg6 : ∀ r, r ≠ .rax → r ≠ .rcx → v6.regs.get r = v.regs.get r := by
      intro r ha hc; rw [r6, Regs.get_set_ne _ _ _ _ (Ne.symm hc), r4]; exact r3 r ha
    have mem6 : v6.mem = v4.mem := by rw [e6]; exact e5.2.1
    obtain ⟨m, u, hr, hus, hurip, hureg, hunew, huoth⟩ := ih (i + 1) v6 (by omega) (by omega) (by rw [e6]; exact h5)
      (by rw [e6]) rcx6 (by rw [reg6 .r13 (by decide) (by decide)]; exact h13) (by rw [reg6 .r14 (by decide) (by decide)]; exact h14)
      (by rw [reg6 .r12 (by decide) (by decide)]; exact h12)
      (by intro j hj; rw [mem6, mem4, rd_write_apart _ _ _ _ (hBE i j hin hj)]; exact hB j hj)
      (by
        intro j hj hj'
        rw [mem6, mem4]
        by_cases hji : j = i
        · subst hji; exact rd_write_same _ _ _
        · rw [rd_write_apart _ _ _ _ (hEE i j hin hj' (Ne.symm hji))]; exact hE j (by omega) hj')
    refine ⟨6 + m, u, by rw [runP_add]; exact hr, hus, hurip, ?_, hunew, ?_⟩
    · intro r ha hc; rw [hureg r ha hc]; exact reg6 r ha hc
    · intro a ha
      rw [huoth a ha, mem6, mem4, rd_write_apart _ _ _ _ (ha i hin)]

/-- **plPre_run.** The loop's room check and setup: RES in 6 steps when `r12 − lo < 8n` (memory and every register but rax, rcx,
    rdx unchanged); otherwise 8 steps reach the loop head with r12 lowered by 8n and rcx = 0. -/
theorem plPre_run {C : Ctx3} {p : Program} {s : Cpu} {n : Nat} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (plPre C ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 16) = lo)
    (hge : lo.toNat ≤ (s.regs.get .r12).toNat) (h8n : 8 * n < 2 ^ 64) (h13 : s.regs.get .r13 = BitVec.ofNat 64 n)
    (hcan : canonical C.res = true) :
    ((s.regs.get .r12).toNat - lo.toNat < 8 * n → ∃ u, runP p 6 s = u ∧ u.stopped = false ∧ u.rip = C.res ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) ∧
    (¬ (s.regs.get .r12).toNat - lo.toNat < 8 * n → ∃ u, runP p 8 s = u ∧ u.stopped = false ∧
        u.rip = s.rip + BitVec.ofNat 64 (bytes C (plPre C)) ∧ u.mem = s.mem ∧
        u.regs.get .r12 = s.regs.get .r12 - slot n ∧ u.regs.get .rcx = 0 ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r12 → u.regs.get r = s.regs.get r) := by
  have c0 : CodeAt C p s.rip (ld .rdx .rbx 16 :: .op (.mov .q (.reg .rax) (.reg .r12)) :: .op (.bin .sub .q (.reg .rax) (.reg .rdx)) ::
      .op (.lea .q .rcx { index := some .r13, scale := .s8 }) :: .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .jccA .b C.res ::
      .op (.bin .sub .q (.reg .r12) (.reg .rcx)) :: movi .rcx 0 :: rest) := by simpa [plPre] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s with hs1
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 := codeAt_next (s' := s1) (by rw [e1]) c0
  have e2 := stepP_mov_rr h1 c1
  set s2 := stepP p s1 with hs2
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 := codeAt_next (s' := s2) (by rw [e2]) c1
  have e3 := stepP_sub_rr h2 c2
  set s3 := stepP p s2 with hs3
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 := codeAt_next (s' := s3) (by rw [e3]) c2
  have e4 := stepP_lea_sc h3 c3
  set s4 := stepP p s3 with hs4
  have h4 : s4.stopped = false := by rw [e4]; exact h3
  have c4 := codeAt_next (s' := s4) (by rw [e4]) c3
  have e5 := stepP_cmp_rr h4 c4
  set s5 := stepP p s4 with hs5
  have h5 : s5.stopped = false := by rw [e5]; exact h4
  have c5 := codeAt_next (s' := s5) (by rw [e5]) c4
  have e6 := stepP_jccA h5 c5 hcan
  set s6 := stepP p s5 with hs6
  have h6 : s6.stopped = false := by rw [e6]; exact h5
  have hr12 := (s.regs.get .r12).isLt
  have rax4 : s4.regs.get .rax = s.regs.get .r12 - lo := by
    rw [e4, e3, e2, e1]
    simp only [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rax by decide), Regs.get_set_same,
      Regs.get_set_ne _ _ _ _ (show GPR.rax ≠ GPR.rdx by decide), Regs.get_set_ne _ _ _ _ (show GPR.rdx ≠ GPR.r12 by decide)]
    rw [hcb]
  have rcx4 : s4.regs.get .rcx = slot n := by
    rw [e4]; simp only [Regs.get_set_same]
    rw [e3, e2, e1]
    simp only [Regs.get_set_ne _ _ _ _ (show GPR.rax ≠ GPR.r13 by decide), Regs.get_set_ne _ _ _ _ (show GPR.rdx ≠ GPR.r13 by decide)]
    rw [h13, ofNat_mul8]
  have hb : Cc.eval .b s5.flags = decide ((s.regs.get .r12).toNat - lo.toNat < 8 * n) := by
    rw [e5, rax4, rcx4, cc_b_of_sub]
    simp only [Value.uval, Value.trunc_q, slot, BitVec.toNat_sub, BitVec.toNat_ofNat]
    congr 1; apply propext
    constructor <;> intro h <;> omega
  have mem5 : s5.mem = s.mem := by rw [e5, e4, e3, e2, e1]
  have reg5 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s5.regs.get r = s.regs.get r := by
    intro r ha hc' hd; rw [e5, e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc'), Regs.get_set_ne _ _ _ _ (Ne.symm hd)]
  constructor
  · intro hlt
    refine ⟨s6, rfl, h6, by rw [e6, hb]; simp [hlt], by rw [e6, mem5], ?_⟩
    intro r ha hc' hd; rw [e6]; exact reg5 r ha hc' hd
  · intro hlt
    have c6 : CodeAt C p s6.rip (.op (.bin .sub .q (.reg .r12) (.reg .rcx)) :: movi .rcx 0 :: rest) := by
      rw [e6, hb]; simp only [hlt, decide_false, Bool.false_eq_true, if_false]; exact codeAt_jcc_fall c5
    have e7 := stepP_sub_rr h6 c6
    set s7 := stepP p s6 with hs7
    have h7 : s7.stopped = false := by rw [e7]; exact h6
    have c7 := codeAt_next (s' := s7) (by rw [e7]) c6
    have e8 := stepP_movi h7 c7
    refine ⟨stepP p s7, rfl, by rw [e8]; exact h7, ?_, by rw [e8, e7, e6, mem5], ?_, by rw [e8]; simp, ?_⟩
    · rw [e8, e7, e6, hb]
      simp only [hlt, decide_false, Bool.false_eq_true, if_false]
      rw [e5, e4, e3, e2, e1]
      simp only [nxt, plPre, ld, movi, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl
    · rw [e8, Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.r12 by decide), e7, Regs.get_set_same]
      rw [show s6.regs = s5.regs by rw [e6], reg5 .r12 (by decide) (by decide) (by decide),
        show s5.regs = s4.regs by rw [e5], rcx4]
    · intro r ha hc' hd h12
      rw [e8, Regs.get_set_ne _ _ _ _ (Ne.symm hc'), e7, Regs.get_set_ne _ _ _ _ (Ne.symm h12), show s6.regs = s5.regs by rw [e6]]
      exact reg5 r ha hc' hd

theorem gen_ne_nil (C : Ctx3) (pc : W) (c : WCode) : gen C pc c ≠ [] := by
  cases c <;> simp [gen]

theorem canon_gen {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {a : W} {c : WCode} {rest : List AI}
    (h : CodeAt C p a (gen C a c ++ rest)) : canonical a = true := by
  obtain ⟨i, l, hil⟩ := List.exists_cons_of_ne_nil (gen_ne_nil C a c)
  rw [hil] at h; exact canon_of_codeAt E h

/-! ## A return into a pending frame -/

/-- **sim_ret_cons.** `ret o` with a pending frame `(c₂, ρ₂)`: the continuation is reached as an R3 run state at `ws ++ ρ₂`, an
    overflow as R3 `ovf`, or RES with the successor state outgrowing ENV (Addendum 9). -/
theorem sim_ret_cons {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {o : WOpd}
    {ρ ρ₂ : List W} {c₂ : WCode} {k' : List (WCode × List W)} {wm : WMem} {s : Cpu}
    (hR : R3 C p L (.run (.ret o) ρ ((c₂, ρ₂) :: k'), wm) s)
    (hneed : need o ≤ L.bufN) {W' : WSt × WMem} (hstep : stepW tbl (.run (.ret o) ρ ((c₂, ρ₂) :: k'), wm) = some W') :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨ (ResExit L (runP p n s) ∧ Common L W'.2 (runP p n s) ∧ RetOver L W'.1)) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hB : s.regs.get .r14 = L.buf := hcom.1
  have hX : s.regs.get .rbx = L.cb := hcom.2.1
  have hL := E.ok
  obtain ⟨q, a, fq, fa, fcode, flo, fhi, fw, frsp, focc, fk⟩ := hfr
  have hc : CodeAt C p s.rip (evalTo C 0 o ++ [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret]) := by
    have h0 := hcode; simp only [gen] at h0; exact h0
  have hpre : EvalPre s 0 L.bufN ρ := ⟨hw, by rw [hB]; exact hL.buf_nowrap,
    fun i j _ hi hj => by rw [hB]; exact buf_env_apart hL hi hlo hhi hj⟩
  have hpost := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) o 0 s _ ρ L.bufN hs hc (by omega) hpre
  simp only [EvalPost] at hpost
  simp only [stepW] at hstep
  cases ho : evalW ρ o with
  | bad => rw [ho] at hstep; cases hstep
  | ovf =>
    rw [ho] at hstep hpost; cases hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := hpost
    obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 (agree_of_frame hB hf1) hf1.2 hs1 hrip1
    exact ⟨n1 + 4, by omega, Or.inl (by rw [runP_add, hr1, hv]; exact hRv)⟩
  | ok ws =>
    rw [ho] at hstep hpost
    simp only [Option.some.injEq] at hstep; subst hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := hpost
    have hlen : ws.length = wid o := evalW_length o ρ ws ho
    have hlenN : ws.length ≤ L.bufN := by rw [hlen]; exact le_trans (wid_le_need o) hneed
    have ag1 : AgreeBuf L s.mem u1.mem := agree_of_frame hB hf1
    have hR := L.rsp0.isLt
    have hst := hL.stk_nowrap
    have hsp := (s.regs.get .rsp).isLt
    set sp := s.regs.get .rsp with hsp_def
    have e8 : (sp + 8).toNat = sp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    have e16 : (sp + 8 + 8).toNat = sp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
    have e16' : sp + 8 + 8 = sp + 16 := by apply BitVec.eq_of_toNat_eq; rw [e16]; simp only [BitVec.toNat_add]; simp; omega
    have m_sp : rd u1.mem sp = q := by rw [ag1 sp (fun i hi => buf_stk_apart hL hi hsl (by omega))]; exact fq
    have m_sp8 : rd u1.mem (sp + 8) = a := by rw [ag1 (sp + 8) (fun i hi => buf_stk_apart hL hi (by omega) (by omega))]; exact fa
    have c1 : CodeAt C p u1.rip [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret] := by rw [hrip1]; exact codeAt_right hc
    have e2 := stepP_movi hs1 c1
    set u2 := stepP p u1 with hu2
    have h2 : u2.stopped = false := by rw [e2]; exact hs1
    have c2 : CodeAt C p u2.rip [.op .ret] := by rw [e2]; exact codeAt_tail c1
    have sp2 : u2.regs.get .rsp = sp := by
      rw [e2]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r13 ≠ GPR.rsp by decide)]
      exact hf1.2 .rsp (by decide) (by decide) (by decide)
    have e3 := stepP_ret h2 c2 (by rw [sp2, show u2.mem = u1.mem by rw [e2], m_sp]; exact canon_of_codeAt E fcode)
    set u3 := stepP p u2 with hu3
    have h3 : u3.stopped = false := by rw [e3]; exact h2
    have rip3 : u3.rip = q := by rw [e3]; simp only [sp2, show u2.mem = u1.mem by rw [e2], m_sp]
    have sp3 : u3.regs.get .rsp = sp + 8 := by rw [e3]; simp [sp2]
    set pc := q + BitVec.ofNat 64 (bytes C [AI.op (.pop .q (.reg .r12))]) with hpc
    have hcont : CodeAt C p q ([AI.op (.pop .q (.reg .r12))] ++ (prependLoop C pc ++ gen C (plExit C pc) c₂)) := by
      have h0 := fcode; simp only [contCode, List.append_assoc] at h0
      rw [plExit_eq, hpc]
      simpa only [bytes_append, ofNat_add64, BitVec.add_assoc] using h0
    have c3 : CodeAt C p u3.rip (.op (.pop .q (.reg .r12)) :: (prependLoop C pc ++ gen C (plExit C pc) c₂)) := by
      rw [rip3]; simpa using hcont
    have e4 := stepP_pop h3 c3 (by decide)
    set u4 := stepP p u3 with hu4
    have h4 : u4.stopped = false := by rw [e4]; exact h3
    have rip4 : u4.rip = pc := by
      rw [e4, rip3, hpc]; simp only [nxt, bytes_cons, bytes_nil, Nat.add_zero]
    have mem4 : u4.mem = u1.mem := by rw [e4, e3, e2]
    have r12_4 : u4.regs.get .r12 = a := by
      rw [e4]; simp only [Regs.get_set_same, sp3, show u3.mem = u1.mem by rw [e3, e2], m_sp8]
    have sp4 : u4.regs.get .rsp = sp + 16 := by
      rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rsp by decide), Regs.get_set_same, sp3, e16']
    have reg4 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r12 → r ≠ .rsp → r ≠ .r13 → u4.regs.get r = s.regs.get r := by
      intro r ha hc' hd h12 hsp' h13
      rw [e4, e3, e2]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm h12), Regs.get_set_ne _ _ _ _ (Ne.symm hsp'), Regs.get_set_ne _ _ _ _ (Ne.symm h13)]
      exact hf1.2 r ha hc' hd
    have r13_4 : u4.regs.get .r13 = BitVec.ofNat 64 ws.length := by
      rw [e4, e3, e2]
      simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.r13 by decide), Regs.get_set_ne _ _ _ _ (show GPR.rsp ≠ GPR.r13 by decide),
        Regs.get_set_same, hlen]
    have rbx4 : u4.regs.get .rbx = L.cb := by
      rw [reg4 .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hX]
    have r14_4 : u4.regs.get .r14 = L.buf := by
      rw [reg4 .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hB]
    -- the frame's state, placed at the continuation's code: an R3 state at (c₂, ρ₂, k')
    have hlo_a : L.envLo.toNat ≤ a.toNat := by omega
    have hsl16 : L.stkLo.toNat ≤ (sp + 16).toNat := by
      have : (sp + 16).toNat = sp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
      omega
    have hcG : CodeAt C p (plExit C pc) (gen C (plExit C pc) c₂) := by
      have := codeAt_right (codeAt_right hcont (a := [AI.op (.pop .q (.reg .r12))])) (a := prependLoop C pc)
      rw [← plExit_eq, show q + BitVec.ofNat 64 (bytes C [AI.op (.pop .q (.reg .r12))]) = pc from rfl] at this
      simpa only [List.append_nil] using codeAt_left (b := []) (by simpa using this)
    obtain ⟨_, _, ⟨hc1, hc2, hc3⟩, hRep⟩ := hcom
    set s4' : Cpu := { u4 with rip := plExit C pc } with hs4'
    have hR4 : R3 C p L (.run c₂ ρ₂ k', wm) s4' := by
      refine ⟨h4, hcG, ⟨r14_4, rbx4, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show rd u4.mem _ = _; rw [mem4, ag1 (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide))]; exact hc1
      · show rd u4.mem _ = _; rw [mem4, ag1 (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
      · show rd u4.mem _ = _; rw [mem4, ag1 (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide))]; exact hc3
      · intro x hx
        show u4.mem.readN x 8 = _
        rw [mem4]
        have := ag1 x (fun i hi => buf_live_apart hL hi hx)
        simp only [rd] at this; rw [this]; exact hRep x hx
      · show L.envLo.toNat ≤ (u4.regs.get .r12).toNat; rw [r12_4]; exact hlo_a
      · show (u4.regs.get .r12).toNat + _ ≤ _; rw [r12_4]; exact fhi
      · show WordsAt u4.mem (u4.regs.get .r12) ρ₂; rw [r12_4, mem4]; exact wordsAt_agree hL ag1 hlo_a fhi fw
      · show Frames C p L u4.mem (u4.regs.get .rsp) (u4.regs.get .r12) k'
        rw [sp4, r12_4, mem4]; exact frames_agree hL ag1 k' (sp + 16) a hlo_a hsl16 fk
      · show L.stkLo.toNat ≤ (u4.regs.get .rsp).toNat; rw [sp4]; exact hsl16
      · show (u4.regs.get .r12).toNat ≤ _ ∧ _; rw [r12_4]; exact focc
    -- the loop's setup
    have hpl : CodeAt C p u4.rip (plPre C ++ (plTest ++ [.jccA .ae (plExit C pc)] ++ plBody ++ [.jmpA (plHead C pc)] ++
        gen C (plExit C pc) c₂)) := by
      have := codeAt_right hcont (a := [AI.op (.pop .q (.reg .r12))])
      rw [rip4]; rw [prependLoop_eq] at this; simpa only [List.append_assoc] using this
    have hbufN := hL.buf_nowrap
    have h8n : 8 * ws.length < 2 ^ 64 := by omega
    have hcb : rd u4.mem (u4.regs.get .rbx + 16) = L.envLo := by
      rw [rbx4, mem4, ag1 (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
    obtain ⟨hRES, hGO⟩ := plPre_run h4 hpl hcb (by rw [r12_4]; exact hlo_a) h8n r13_4 (canon_of_codeAt E E.res)
    rw [r12_4] at hRES hGO
    by_cases hlt : a.toNat - L.envLo.toNat < 8 * ws.length
    · obtain ⟨u5, hr5, hs5, hrip5, hm5, hreg5⟩ := hRES hlt
      obtain ⟨v, hv, hres, hcomv, hover⟩ := res_exit (n := ws.length) E hR4 (u := u5)
        (fun x _ => by rw [hm5]) (fun r ha hc' hd => hreg5 r ha hc' hd) hs5 hrip5 (by show (u4.regs.get .r12).toNat - _ < _; rw [r12_4]; exact hlt)
      refine ⟨n1 + 3 + 6 + 4, by omega, Or.inr ⟨?_, ?_, ?_⟩⟩
      · rw [runP_add, runP_add, runP_add, hr1]; show ResExit L (runP p 4 (runP p 6 u4)); rw [hr5, hv]; exact hres
      · rw [runP_add, runP_add, runP_add, hr1]; show Common L wm (runP p 4 (runP p 6 u4)); rw [hr5, hv]; exact hcomv
      · simp only [RetOver, EnvOver, List.length_append] at hover ⊢; omega
    · obtain ⟨u5, hr5, hs5, hrip5, hm5, h12_5, hcx5, hreg5⟩ := hGO hlt
      set e := a - slot ws.length with he
      have heN : e.toNat = a.toNat - 8 * ws.length := by
        simp only [he, slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hTop := L.envTop.isLt
      have hBE : ∀ j j', j < ws.length → j' < ws.length → VIRBridge.Apart (e + slot j) (L.buf + slot j') :=
        fun j j' hj hj' => (buf_env_apart hL (by omega : j' < L.bufN) (n := ws.length) (by rw [heN]; omega)
          (by rw [heN]; omega) hj).symm'
      have hEE : ∀ j j', j < ws.length → j' < ws.length → j ≠ j' → VIRBridge.Apart (e + slot j) (e + slot j') :=
        fun j j' hj hj' hne => slot_apart (b := e) (N := ws.length) (by rw [heN]; omega) hj hj' hne
      have hloop : CodeAt C p (plHead C pc) (plTest ++ [.jccA .ae (plExit C pc)] ++ plBody ++ [.jmpA (plHead C pc)]) := by
        have := codeAt_right hpl; rw [rip4] at this
        have h1 : CodeAt C p (pc + BitVec.ofNat 64 (bytes C (plPre C)))
            ((plTest ++ [.jccA .ae (plExit C pc)] ++ plBody ++ [.jmpA (plHead C pc)]) ++ gen C (plExit C pc) c₂) := by
          simpa only [List.append_assoc] using this
        exact codeAt_left h1
      have hch : canonical (plHead C pc) = true := canon_of_codeAt E (l := _) (i := .op (.bin .cmp .q (.reg .rcx) (.reg .r13)))
        (by simpa [plTest] using hloop)
      have hcx : canonical (plExit C pc) = true := canon_gen E (rest := []) (by simpa using hcG)
      obtain ⟨m, u6, hr6, hs6, hrip6, hreg6, hnew6, hoth6⟩ := loop_run hloop hcx hch h8n hBE hEE ws.length 0 u5 (by omega)
        (by omega) hs5 (by rw [hrip5, rip4]; rfl) (by rw [hcx5]; rfl)
        (by rw [hreg5 .r13 (by decide) (by decide) (by decide) (by decide)]; exact r13_4)
        (by rw [hreg5 .r14 (by decide) (by decide) (by decide) (by decide)]; exact r14_4) h12_5
        (by
          intro j hj; rw [hm5, mem4]
          have := (wordsAt_slot.mp hw1) j hj; rw [hB] at this; simpa using this)
        (fun j hj _ => absurd hj (Nat.not_lt_zero j))
      have hR6 : R3 C p L (.run c₂ (ws ++ ρ₂) k', wm) u6 := by
        refine r3_of_prepend hL hR4 (by show _ ≤ (u4.regs.get .r12).toNat; rw [r12_4]; omega) ?_ ?_ ?_ ?_ hs6 (by rw [hrip6]; exact hcG)
        · show u6.regs.get .r12 = u4.regs.get .r12 - _
          rw [hreg6 .r12 (by decide) (by decide), h12_5, r12_4]
        · intro j hj; show rd u6.mem (u4.regs.get .r12 - _ + _) = _; rw [r12_4]; exact hnew6 j hj
        · intro x _ hx
          show rd u6.mem x = rd u4.mem x
          rw [hoth6 x (by intro j hj; have := hx j hj; rw [show s4'.regs.get .r12 = a from r12_4] at this; exact this), hm5]
        · intro r ha hc' hd h12
          show u6.regs.get r = u4.regs.get r
          rw [hreg6 r ha hc', hreg5 r ha hc' hd h12]
      refine ⟨n1 + 3 + 8 + m, by omega, Or.inl ?_⟩
      rw [runP_add, runP_add, runP_add, hr1]
      show R3 C p L _ (runP p m (runP p 8 u4))
      rw [hr5, hr6]; exact hR6

/-- **sim_ret.** A word step of `ret o` is simulated: DONE at the driver, the continuation as an R3 run state, an overflow as R3
    `ovf`, or RES with the successor state outgrowing ENV (Addendum 9). -/
theorem sim_ret {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {o : WOpd}
    {ρ : List W} {k : List (WCode × List W)} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.ret o) ρ k, wm) s)
    (hneed : need o ≤ L.bufN) {W' : WSt × WMem} (hstep : stepW tbl (.run (.ret o) ρ k, wm) = some W') :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨ (ResExit L (runP p n s) ∧ Common L W'.2 (runP p n s) ∧ RetOver L W'.1)) := by
  match k, hR, hstep with
  | [], hR, hstep =>
    obtain ⟨n, hn, h⟩ := sim_ret_nil E hR hneed hstep
    exact ⟨n, hn, Or.inl h⟩
  | (c₂, ρ₂) :: k', hR, hstep => exact sim_ret_cons E hR hneed hstep

end S3
