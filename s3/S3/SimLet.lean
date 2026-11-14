/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 10): the word step `letE c₁ c₂`. STACK's room check, `push r12`, then
  `call c₁`: c₁ is reached as an R3 run state with the pending frame (c₂, ρ) on top, or RES with the successor's continuations
  outgrowing STACK (`StkOver`). A separate module beside Sim3 and SimRet, which it imports and does not edit.
-/
import S3.SimRet

namespace S3
open VIRC X86

theorem stepP_push {C : Ctx3} {p : Program} {s : Cpu} {r : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.push .q (.reg r)) :: l)) :
    stepP p s = { s with mem := s.mem.writeSize .q (s.regs.get .rsp - 8) (s.regs.get r), regs := s.regs.set .rsp (s.regs.get .rsp - 8), rip := nxt C s.rip (.op (.push .q (.reg r))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_push_reg .q r (live_of hs)]
  simp [Cpu.getReg, Size.bytes, nxt, AI.size]

theorem stepP_callA {C : Ctx3} {p : Program} {s : Cpu} {a : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.callA a :: l)) (hcan : canonical a = true) :
    stepP p s = { s with mem := s.mem.writeSize .q (s.regs.get .rsp - 8) (s.rip + 5), regs := s.regs.set .rsp (s.regs.get .rsp - 8), rip := a } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  have e : s.rip + BitVec.ofNat 64 5 + (a - (s.rip + 5)) = a := by bv_omega
  rw [step_call_rel _ (live_of hs) (by have h := hcan; rw [← e] at h; exact h)]
  simp [add_sub_self']

/-- **stackRoom_run.** STACK's room check: in 5 steps it reaches RES exactly when `rsp − stkLo < 16`, and otherwise falls
    through; memory unchanged, registers other than rax, rcx unchanged. -/
theorem stackRoom_run {C : Ctx3} {p : Program} {s : Cpu} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (stackRoom C ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 24) = lo)
    (hge : lo.toNat ≤ (s.regs.get .rsp).toNat) (hcan : canonical C.res = true) :
    ∃ u, runP p 5 s = u ∧ u.stopped = false ∧ u.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
      u.rip = (if (s.regs.get .rsp).toNat - lo.toNat < 16 then C.res else s.rip + BitVec.ofNat 64 (bytes C (stackRoom C))) := by
  have c0 : CodeAt C p s.rip (ld .rcx .rbx 24 :: .op (.mov .q (.reg .rax) (.reg .rsp)) :: .op (.bin .sub .q (.reg .rax) (.reg .rcx)) ::
      .op (.bin .cmp .q (.reg .rax) (.imm 16)) :: .jccA .b C.res :: rest) := by simpa [stackRoom] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 := codeAt_next (s' := s1) (by rw [e1]) c0
  have e2 := stepP_mov_rr h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 := codeAt_next (s' := s2) (by rw [e2]) c1
  have e3 := stepP_sub_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 := codeAt_next (s' := s3) (by rw [e3]) c2
  have e4 := stepP_cmp_ri h3 c3
  set s4 := stepP p s3
  have h4 : s4.stopped = false := by rw [e4]; exact h3
  have c4 := codeAt_next (s' := s4) (by rw [e4]) c3
  have e5 := stepP_jccA h4 c4 hcan
  have rax3 : s3.regs.get .rax = s.regs.get .rsp - lo := by
    rw [e3, e2, e1]; simp only [Regs.get_set_same, Regs.get_set_ne _ _ _ _ (show GPR.rax ≠ GPR.rcx by decide),
      Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rsp by decide), Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rbx by decide)]
    rw [hcb]
  have h16 : (16 : W).toNat = 16 := rfl
  have hb : Cc.eval .b s4.flags = decide ((s.regs.get .rsp).toNat - lo.toNat < 16) := by
    rw [e4, rax3, cc_b_of_sub]
    simp only [Value.uval, Value.trunc_q, BitVec.toNat_sub, h16]
    congr 1; apply propext
    have := (s.regs.get .rsp).isLt
    constructor <;> intro h <;> omega
  refine ⟨stepP p s4, rfl, by rw [e5]; exact h4, by rw [e5, e4, e3, e2, e1], ?_, ?_⟩
  · intro r ha hc'; rw [e5, e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  · rw [e5, hb]
    by_cases hlt : (s.regs.get .rsp).toNat - lo.toNat < 16
    · simp [hlt]
    · simp only [hlt, decide_false, Bool.false_eq_true, if_false]
      rw [e4, e3, e2, e1]
      simp only [nxt, stackRoom, ld, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl

/-- **frames_above.** A frame chain reads no stack word below its own `rsp`: agreement at and above `sp0` on STACK, and at and
    above `lo0` in ENV, keeps it. -/
theorem frames_above {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {sp0 lo0 : W} {m m' : Mem}
    (hstk : ∀ x, sp0.toNat ≤ x.toNat → x.toNat ≤ L.rsp0.toNat → rd m' x = rd m x)
    (henv : ∀ x, lo0.toNat ≤ x.toNat → x.toNat + 8 ≤ L.envTop.toNat → rd m' x = rd m x) :
    ∀ (k : List (WCode × List W)) (rsp lo : W), lo0.toNat ≤ lo.toNat → sp0.toNat ≤ rsp.toNat →
      Frames C p L m rsp lo k → Frames C p L m' rsp lo k
  | [], rsp, lo, hel, hsl, ⟨h1, h2, h3, h4, h5, h6⟩ => by
    have hR := L.rsp0.isLt
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    refine ⟨?_, h2, ?_, h4, ?_, h6⟩
    · rw [hstk rsp hsl (by omega)]; exact h1
    · rw [hstk (rsp + 8) (by omega) (by omega)]; exact h3
    · rw [hstk L.rsp0 (by omega) (le_refl _)]; exact h5
  | (c, ρ) :: k, rsp, lo, hel, hsl, ⟨q, a, h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ => by
    have hR := L.rsp0.isLt
    have hT := L.envTop.isLt
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    have e16 : (rsp + 16).toNat = rsp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
    have hw : WordsAt m' a ρ := by
      intro j hj
      have he : (a + BitVec.ofNat 64 (8 * j)).toNat = a.toNat + 8 * j := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have := henv (a + BitVec.ofNat 64 (8 * j)) (by omega) (by omega)
      simp only [rd] at this; rw [this]; exact h6 j hj
    refine ⟨q, a, ?_, ?_, h3, h4, h5, hw, h7, h9, frames_above hL hstk henv k (rsp + 16) a (by omega) (by omega) h8⟩
    · rw [hstk rsp hsl (by omega)]; exact h1
    · rw [hstk (rsp + 8) (by omega) (by omega)]; exact h2

/-- Addendum 10: the successor's continuations, with the entry slot, outgrow STACK. -/
def StkOver (L : Lay3) (k : List (WCode × List W)) : Prop :=
  L.rsp0.toNat + 8 - L.stkLo.toNat < 16 * (k.length + 1) + 8

/-- **sim_letE.** A word step of `letE c₁ c₂` is simulated: c₁ is reached as an R3 run state with (c₂, ρ) pending, or RES with
    the successor's continuations outgrowing STACK (Addendum 10). -/
theorem sim_letE {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {c₁ c₂ : WCode}
    {ρ : List W} {k : List (WCode × List W)} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.letE c₁ c₂) ρ k, wm) s)
    {W' : WSt × WMem} (hstep : stepW tbl (.run (.letE c₁ c₂) ρ k, wm) = some W') :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨ (ResExit L (runP p n s) ∧ Common L W'.2 (runP p n s) ∧ StkOver L ((c₂, ρ) :: k))) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hcom0 := hcom
  obtain ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩ := hcom
  have hL := E.ok
  simp only [stepW, Option.some.injEq] at hstep; subst hstep
  set pre : List AI := stackRoom C ++ [.op (.push .q (.reg .r12))] with hpre
  set pAfter := s.rip + BitVec.ofNat 64 (bytes C pre + 5) with hpA
  set p₂ := pAfter + BitVec.ofNat 64 (bytes C ([.op (.pop .q (.reg .r12))] ++
        prependLoop C (pAfter + BitVec.ofNat 64 (bytes C [.op (.pop .q (.reg .r12))])))) with hp₂
  set p₁ := p₂ + BitVec.ofNat 64 (bytes C (gen C p₂ c₂)) with hp₁
  have hc0 : CodeAt C p s.rip (stackRoom C ++ ([.op (.push .q (.reg .r12))] ++ ([.callA p₁] ++ (contCode C pAfter c₂ ++ gen C p₁ c₁)))) := by
    have h0 := hcode; rw [gen_letE] at h0; simpa only [List.append_assoc] using h0
  have hcb : rd s.mem (s.regs.get .rbx + 24) = L.stkLo := by rw [hX]; exact hc3
  obtain ⟨u1, hr1, hs1, hm1, hreg1, hrip1⟩ := stackRoom_run hs hc0 hcb hsl (canon_of_codeAt E E.res)
  have hR := L.rsp0.isLt
  have hst := hL.stk_nowrap
  set sp := s.regs.get .rsp with hsp_def
  have hfb := frames_bound k sp _ hfr
  by_cases hlt : sp.toNat - L.stkLo.toNat < 16
  · rw [if_pos hlt] at hrip1
    have hret : rd u1.mem L.rsp0 = L.ret0 := by rw [hm1]; exact frames_ret0 k _ _ hfr
    obtain ⟨v, hv, hres, hcomv⟩ := exit_run (rest := []) hL hs1 (by rw [hrip1]; simpa using E.res)
      (common_of_buf hL hcom0 (fun x _ => by rw [hm1]) (fun r ha hc' _ => hreg1 r ha hc')) hret E.ret_canon
    refine ⟨5 + 4, by omega, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [runP_add, hr1, hv]; exact hres
    · rw [runP_add, hr1, hv]; exact hcomv
    · simp only [StkOver, List.length_cons]; have := hL.stk_lo_le; omega
  · rw [if_neg hlt] at hrip1
    have c1 : CodeAt C p u1.rip (.op (.push .q (.reg .r12)) :: ([.callA p₁] ++ (contCode C pAfter c₂ ++ gen C p₁ c₁))) := by
      rw [hrip1]; simpa using codeAt_right hc0
    have e2 := stepP_push hs1 c1
    set u2 := stepP p u1 with hu2
    have h2 : u2.stopped = false := by rw [e2]; exact hs1
    have c2 : CodeAt C p u2.rip (.callA p₁ :: (contCode C pAfter c₂ ++ gen C p₁ c₁)) := by
      rw [e2]; simpa using codeAt_tail c1
    have hcG1 : CodeAt C p p₁ (gen C p₁ c₁) := by
      have := codeAt_right (codeAt_tail c2) (a := contCode C pAfter c₂)
      have e : u2.rip + BitVec.ofNat 64 (AI.size C (.callA p₁)) + BitVec.ofNat 64 (bytes C (contCode C pAfter c₂)) = p₁ := by
        rw [e2, hrip1, hp₁, hp₂, hpA, hpre]
        simp only [nxt, contCode, bytes_gen, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
        all_goals rfl
      rw [e] at this; exact this
    have hcK : CodeAt C p pAfter (contCode C pAfter c₂) := by
      have := codeAt_left (codeAt_tail c2) (b := gen C p₁ c₁)
      have e : u2.rip + BitVec.ofNat 64 (AI.size C (.callA p₁)) = pAfter := by
        rw [e2, hrip1, hpA, hpre]
        simp only [nxt, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
        all_goals rfl
      rw [e] at this; exact this
    have e3 := stepP_callA h2 c2 (canon_gen E (rest := []) (by simpa using hcG1))
    set u3 := stepP p u2 with hu3
    have ret3 : u2.rip + 5 = pAfter := by
      rw [e2, hrip1, hpA, hpre]
      simp only [nxt, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl
    have sp1 : u1.regs.get .rsp = sp := hreg1 .rsp (by decide) (by decide)
    have r12_1 : u1.regs.get .r12 = s.regs.get .r12 := hreg1 .r12 (by decide) (by decide)
    have sp2 : u2.regs.get .rsp = sp - 8 := by rw [e2]; simp [sp1]
    have mem3 : u3.mem = (s.mem.writeSize .q (sp - 8) (s.regs.get .r12)).writeSize .q (sp - 8 - 8) pAfter := by
      rw [e3, sp2, ret3, show u2.mem = s.mem.writeSize .q (sp - 8) (s.regs.get .r12) by rw [e2]; simp [sp1, r12_1, hm1]]
    have sp3 : u3.regs.get .rsp = sp - 16 := by
      rw [e3]; simp only [Regs.get_set_same, sp2]; bv_omega
    have reg3 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsp → u3.regs.get r = s.regs.get r := by
      intro r ha hc' hsp'
      rw [e3, e2]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hsp')]; exact hreg1 r ha hc'
    -- the two stack words
    have hsp := sp.isLt
    have nsp8 : (sp - 8).toNat = sp.toNat - 8 := by simp only [BitVec.toNat_sub]; simp; omega
    have nsp16 : (sp - 8 - 8).toNat = sp.toNat - 16 := by simp only [BitVec.toNat_sub]; simp; omega
    have e88 : sp - 8 - 8 = sp - 16 := by bv_omega
    have h8w : (8 : W).toNat = 8 := rfl
    have h16w : (16 : W).toNat = 16 := rfl
    have r16 : sp - 16 + 8 = sp - 8 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, ← e88, nsp16, nsp8, h8w]; omega
    have s16 : sp - 16 + 16 = sp := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, ← e88, nsp16, h16w]; omega
    have w8 : ∀ j, j < 8 → inStk L (sp - 8 + BitVec.ofNat 64 j) := stk_word L (by omega) (by omega) hL
    have w16 : ∀ j, j < 8 → inStk L (sp - 8 - 8 + BitVec.ofNat 64 j) := stk_word L (by omega) (by omega) hL
    have hmem : ∀ x, VIRBridge.Apart (sp - 8) x → VIRBridge.Apart (sp - 8 - 8) x → rd u3.mem x = rd s.mem x := by
      intro x h8 h16; rw [mem3, rd_write_apart _ _ _ _ h16, rd_write_apart _ _ _ _ h8]
    have stk_cb : ∀ m, m < 4 → ∀ x : W, (∀ j, j < 8 → inStk L (x + BitVec.ofNat 64 j)) →
        VIRBridge.Apart x (L.cb + BitVec.ofNat 64 (8 * m)) := fun m hm x hx => apart_of_disjoint hL.stk_cb hx (cb_word L hm)
    have cbm : ∀ m, m < 4 → rd u3.mem (L.cb + BitVec.ofNat 64 (8 * m)) = rd s.mem (L.cb + BitVec.ofNat 64 (8 * m)) :=
      fun m hm => hmem _ (stk_cb m hm _ w8) (stk_cb m hm _ w16)
    have envm : ∀ x : W, L.envLo.toNat ≤ x.toNat → x.toNat + 8 ≤ L.envTop.toNat → rd u3.mem x = rd s.mem x := by
      intro x h1 h2
      have hx : ∀ j, j < 8 → inEnv L (x + BitVec.ofNat 64 j) := by
        intro j hj
        have : (x + BitVec.ofNat 64 j).toNat = x.toNat + j := by
          have := L.envTop.isLt; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        simp only [inEnv, this]; omega
      exact hmem x (apart_of_disjoint (fun a h3 h4 => hL.env_stk a h4 h3) w8 hx) (apart_of_disjoint (fun a h3 h4 => hL.env_stk a h4 h3) w16 hx)
    refine ⟨5 + 2, by omega, Or.inl ?_⟩
    rw [runP_add, hr1]
    show R3 C p L _ u3
    have rip3 : u3.rip = p₁ := by rw [e3]
    refine ⟨by rw [e3]; exact h2, by rw [rip3]; exact hcG1,
      ⟨by rw [reg3 .r14 (by decide) (by decide) (by decide), hB], by rw [reg3 .rbx (by decide) (by decide) (by decide), hX],
        ⟨by rw [show L.cb + 8 = L.cb + BitVec.ofNat 64 (8 * 1) from rfl, cbm 1 (by decide)]; exact hc1,
         by rw [show L.cb + 16 = L.cb + BitVec.ofNat 64 (8 * 2) from rfl, cbm 2 (by decide)]; exact hc2,
         by rw [show L.cb + 24 = L.cb + BitVec.ofNat 64 (8 * 3) from rfl, cbm 3 (by decide)]; exact hc3⟩, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h := hmem x (apart_of_disjoint hL.stk_live w8 (live_word L hx)) (apart_of_disjoint hL.stk_live w16 (live_word L hx))
      simp only [rd] at h; rw [h]; exact hRep x hx
    · rw [reg3 .r12 (by decide) (by decide) (by decide)]; exact hlo
    · rw [reg3 .r12 (by decide) (by decide) (by decide)]; exact hhi
    · rw [reg3 .r12 (by decide) (by decide) (by decide)]
      intro j hj
      have hT := L.envTop.isLt
      have he : (s.regs.get .r12 + BitVec.ofNat 64 (8 * j)).toNat = (s.regs.get .r12).toNat + 8 * j := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have := envm (s.regs.get .r12 + BitVec.ofNat 64 (8 * j)) (by omega) (by omega)
      simp only [rd] at this; rw [this]; exact hw j hj
    · rw [sp3, reg3 .r12 (by decide) (by decide) (by decide)]
      have n16 : (sp - 16).toNat = sp.toNat - 16 := by rw [← e88]; exact nsp16
      refine ⟨pAfter, s.regs.get .r12, ?_, ?_, hcK, le_refl _, hhi, ?_, by omega, ?_, ?_⟩
      · rw [mem3, ← e88]; exact rd_write_same _ _ _
      · rw [mem3, r16, rd_write_apart _ _ _ _ (order_apart (by rw [nsp16, nsp8]; omega) (by omega))]
        exact rd_write_same _ _ _
      · intro j hj
        have hT := L.envTop.isLt
        have he : (s.regs.get .r12 + BitVec.ofNat 64 (8 * j)).toNat = (s.regs.get .r12).toNat + 8 * j := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have := envm (s.regs.get .r12 + BitVec.ofNat 64 (8 * j)) (by omega) (by omega)
        simp only [rd] at this; rw [this]; exact hw j hj
      · exact hocc
      · rw [s16]
        refine frames_above hL (sp0 := sp) (lo0 := L.envLo) ?_ envm k sp _ hlo (le_refl _) hfr
        intro x h1 h2
        exact hmem x (order_apart (by rw [nsp8]; omega) (by omega)) (order_apart (by rw [nsp16]; omega) (by omega))
    · rw [sp3]; rw [← e88, nsp16]; omega
    · rw [reg3 .r12 (by decide) (by decide) (by decide)]
      simp only [kSize]; exact ⟨hocc.1, by omega⟩

end S3
