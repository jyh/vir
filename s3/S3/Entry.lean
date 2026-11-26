/-
  O95, OBJECT-NOCHECK-ENTRY (amend-27; errata E1, E2), route file 3: the entry stub. After the decider's code returns to ret0, a test of
  BUF[2] (the decider's `bool`, = 1 to ACCEPT), then Driver3's `loopTail env0 XF H₂` (status test, BUF[0..1] → ENV, jump to H₂), and at
  H₂ `call base_e`. A new file (NE4).
-/
import S3.Driver3
import S3.Contain
import S3.ReadOnly

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- The bool test: BUF[2] into rax, compare with 1, leave to XF unless equal. -/
def boolChk (XF : W) : List AI := [ld .rax .r14 16, movi .rcx 1, .op (.bin .cmp .q (.reg .rax) (.reg .rcx)), .jccA .ne XF]

/-- The stub after the decider returns (at ret0): the bool test, then `loopTail`. -/
def gateTail (env0 XF H₂ : W) : List AI := boolChk XF ++ loopTail env0 XF H₂

/-- **bool_check.** The bool test's four steps: memory unchanged, rax/rcx clobbered, and XF unless BUF[2] = 1. -/
theorem bool_check {C : Ctx3} {p : Program} {L : Lay3} {wm : WMem} {u : Cpu} {XF : W} {l : List AI}
    (hs : u.stopped = false) (hc : CodeAt C p u.rip (boolChk XF ++ l)) (hcm : Common L wm u) (hX : canonical XF = true) :
    ∃ v, runP p 4 u = v ∧ v.stopped = false ∧ v.mem = u.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → v.regs.get r = u.regs.get r) ∧
      v.rip = (if rd u.mem (L.buf + 16) = 1 then u.rip + BitVec.ofNat 64 (bytes C (boolChk XF)) else XF) := by
  have c0 : CodeAt C p u.rip (ld .rax .r14 16 :: movi .rcx 1 :: .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .jccA .ne XF :: l) := by
    simpa [boolChk] using hc
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
  have hr14 : u.regs.get .r14 = L.buf := hcm.1
  have rax2 : s2.regs.get .rax = rd u.mem (L.buf + 16) := by
    rw [e2, e1]
    simp only [Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rax by decide), Regs.get_set_same, hr14]
  have rcx2 : s2.regs.get .rcx = 1 := by rw [e2]; simp
  have hne : Cc.eval .ne s3.flags = !decide (rd u.mem (L.buf + 16) = 1) := by
    rw [e3, rax2, rcx2, cc_ne_sub]
  refine ⟨stepP p s3, rfl, by rw [e4]; exact h3, by rw [e4, e3, e2, e1], ?_, ?_⟩
  · intro r ha hc'; rw [e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  · rw [e4, hne]
    by_cases h0 : rd u.mem (L.buf + 16) = 1
    · rw [if_pos h0]
      simp only [h0, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [e3, e2, e1]
      simp only [nxt, boolChk, ld, movi, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl
    · rw [if_neg h0]; simp only [Bool.not_eq_true', decide_eq_false_iff_not, h0, not_false_eq_true, if_true]

/-- A layout with its return point re-pointed (`Lay3.Ok`, `Common`, `AtHead` and `DriverCall` other than `ret` do not read `ret0`). -/
def Lay3.reRet (L : Lay3) (r s : W) : Lay3 := { L with ret0 := r, stubRet := s }

theorem reRet_ok {L : Lay3} (hL : L.Ok) (r s : W) : (L.reRet r s).Ok := by
  cases hL; constructor <;> assumption

theorem reRet_common {L : Lay3} {wm : WMem} {u : Cpu} (r s : W) (h : Common L wm u) : Common (L.reRet r s) wm u := h

theorem reRet_atHead {L : Lay3} {H : W} {ρ : List W} {wm : WMem} {u : Cpu} (r s : W) (h : AtHead L H ρ wm u) :
    AtHead (L.reRet r s) H ρ wm u := ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12⟩

/-- **gate_accept.** After the decider's DONE return with BUF = [w0, w1, 1]: 14 steps reach H₂ in AtHead with ENV = [w0, w1]. -/
theorem gate_accept {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {XF H₂ w0 w1 : W} {wm : WMem} {u : Cpu}
    (hR : Returned L stDone u) (hcm : Common L wm u) (hbuf : WordsAt u.mem L.buf [w0, w1, 1])
    (hc : CodeAt C p u.rip (gateTail L.env0 XF H₂)) (hX : canonical XF = true) (hH : canonical H₂ = true) (hN : 2 ≤ L.bufN)
    (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat) :
    ∃ w, runP p 14 u = w ∧ AtHead L H₂ [w0, w1] wm w := by
  obtain ⟨hus, hurip, hursp, hcb⟩ := hR
  have h2 : rd u.mem (L.buf + 16) = 1 := by
    have := hbuf 2 (by simp); simpa [rd] using this
  obtain ⟨v, hv, hvs, hvm, hvr, hvrip⟩ := bool_check (L := L) hus (by simpa only [gateTail] using hc) hcm hX
  rw [if_pos h2] at hvrip
  have hcv : CodeAt C p v.rip (loopTail L.env0 XF H₂) := by
    rw [hvrip]; exact codeAt_right (by simpa only [gateTail] using hc)
  let L' := L.reRet v.rip L.stubRet
  have hRv : Returned L' stDone v :=
    ⟨hvs, rfl, by rw [hvr .rsp (by decide) (by decide)]; exact hursp, by rw [hvm]; exact hcb⟩
  have hcmv : Common L' wm v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hvr .r14 (by decide) (by decide)]; exact hcm.1
    · rw [hvr .rbx (by decide) (by decide)]; exact hcm.2.1
    · rw [hvm]; exact hcm.2.2.1
    · rw [hvm]; exact hcm.2.2.2
  have hbv : WordsAt v.mem L.buf [w0, w1] := by
    intro j hj; rw [hvm]; simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact hbuf 0 (by simp)
    | 1, _ => exact hbuf 1 (by simp)
  obtain ⟨w, hw, hA⟩ := after_done (C := C) (p := p) (L := L') (reRet_ok hL _ _) hRv hcmv hbv hcv hX hH hN hE hstk
  refine ⟨w, by rw [show (14 : Nat) = 4 + 10 from rfl, runP_add, hv, hw], ?_⟩
  exact ⟨hA.1, hA.2, hA.3, hA.4, hA.5, hA.6, hA.7, hA.8, hA.9, hA.10, hA.11, hA.12⟩

/-- **gate_reject.** After the decider returns with any status, if the stub does not reach H₂ it reaches XF with memory unchanged:
    a non-DONE status, or DONE with BUF[2] ≠ 1. -/
theorem gate_reject {C : Ctx3} {p : Program} {L : Lay3} {XF H₂ code : W} {wm : WMem} {u : Cpu}
    (hR : Returned L code u) (hcm : Common L wm u) (hc : CodeAt C p u.rip (gateTail L.env0 XF H₂)) (hX : canonical XF = true)
    (hrej : code ≠ 0 ∨ rd u.mem (L.buf + 16) ≠ 1) :
    ∃ n v, runP p n u = v ∧ v.stopped = false ∧ v.rip = XF ∧ v.mem = u.mem := by
  obtain ⟨hus, hurip, hursp, hcb⟩ := hR
  obtain ⟨v, hv, hvs, hvm, hvr, hvrip⟩ := bool_check (L := L) hus (by simpa only [gateTail] using hc) hcm hX
  by_cases h2 : rd u.mem (L.buf + 16) = 1
  · rw [if_pos h2] at hvrip
    have hne : code ≠ 0 := by rcases hrej with h | h; exact h; exact absurd h2 h
    have hcv : CodeAt C p v.rip (loopTail L.env0 XF H₂) := by
      rw [hvrip]; exact codeAt_right (by simpa only [gateTail] using hc)
    have hcmv : Common L wm v := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hvr .r14 (by decide) (by decide)]; exact hcm.1
      · rw [hvr .rbx (by decide) (by decide)]; exact hcm.2.1
      · rw [hvm]; exact hcm.2.2.1
      · rw [hvm]; exact hcm.2.2.2
    obtain ⟨x, hx, hxs, hxm, -, hxrip⟩ := loop_check hvs hcv hcmv hX
    rw [if_neg (by rw [hvm, hcb]; exact hne)] at hxrip
    exact ⟨4 + 4, x, by rw [runP_add, hv, hx], hxs, hxrip, by rw [hxm, hvm]⟩
  · rw [if_neg h2] at hvrip
    exact ⟨4, v, hv, hvs, hvrip, hvm⟩

/-- **compile_x86S.** `compile_x86` for a program p that CONTAINS `lower3`'s code (`hsub`), with the RES side keeping `Common` at the
    word state after the step (as `s3_refines_from_s2` gives it), so a caller can run code after a RES return. -/
theorem compile_x86S {lay : Int → W} {σ : VIRL2.Store} {m : WMem} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂)
    (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfB true ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base)
    (hsub : ∀ a i, (lower3B true ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1) < 2 ^ 64)
    (hNm : needW (lower2T Γ₀ e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T Γ₀ e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {s : Cpu} (hD : DriverCall L ρw₀ m s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) :
    (∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
      (∃ W', (∃ k, WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W') ∧ R3 C p L W' (runP p mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr Wr', WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧
        stepW (lower2T Γ₀ e []).2 Wr = some Wr' ∧ ResExit L (runP p mm s) ∧ Common L Wr'.2 (runP p mm s))) ∧
    (∀ S, Steps₂ (instL 0 vs e, σ) S → Faults S → ∃ mm,
      (∃ W', (∃ k, WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W') ∧ R3 C p L W' (runP p mm s) ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∨
      (∃ j Wr Wr', WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧
        stepW (lower2T Γ₀ e []).2 Wr = some Wr' ∧ ResExit L (runP p mm s) ∧ Common L Wr'.2 (runP p mm s))) ∧
    (∀ n S, SrcN n (instL 0 vs e, σ) S → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧ (n ≤ mm ∨ W'.1 = .ovf)) ∨
      (∃ j Wr Wr', WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧
        stepW (lower2T Γ₀ e []).2 Wr = some Wr' ∧ ResExit L (runP p mm s) ∧ Common L Wr'.2 (runP p mm s))) := by
  have h0 := s2_init Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok he hl hm
  have lift := fun {k} {Wf} (hrun : WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wf) =>
    s3_refines_from_s2S (b := true) (I₀ := (.run (lowerT e) (vs.map valOf) [], σ)) hCdef hsub hC hb hT hNm hNt hL hcanon hretc
      hstub hD hrip h0 hlive (fun hc => by subst hCdef; simp [ctxOfB] at hc) hrun
  obtain ⟨c1, c2, c3⟩ := compile_refines Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm
  refine ⟨fun a σ' w hs hw' => ?_, fun S hs hF => ?_, fun n S hn => ?_⟩
  · obtain ⟨k, W', hW, hP⟩ := c1 a σ' w hs hw'
    obtain ⟨mm, ⟨-, hR⟩ | ⟨Wr, Wr', j, hj, hst, -, hres, hcm⟩⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', ⟨k, hW⟩, hR, hP⟩⟩
    · exact ⟨mm, .inr ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩
  · obtain ⟨k, W', hW, hP⟩ := c2 S hs hF
    obtain ⟨mm, ⟨-, hR⟩ | ⟨Wr, Wr', j, hj, hst, -, hres, hcm⟩⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', ⟨k, hW⟩, hR, hP⟩⟩
    · exact ⟨mm, .inr ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩
  · obtain ⟨k, W', hW, hP⟩ := c3 n S hn
    obtain ⟨mm, ⟨hk, hR⟩ | ⟨Wr, Wr', j, hj, hst, -, hres, hcm⟩⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hP.imp (fun h => by omega) id⟩⟩
    · exact ⟨mm, .inr ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩

/-- The capability's two words, as the driver passes them. -/
theorem envRel_cap {T : Table} {lay : Int → W} {σ : Store} {p : Int} {n : Nat} (hR : σ.R.lookup p = some n) :
    EnvRel T lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) [lay p, BitVec.ofNat 64 n] := by
  have h := EnvRel.cons (T := T) (lay := lay) (Γ := []) (ρ := []) (ρw := []) (VRel.cap (T := T) (lay := lay) hR) .nil
  simpa [valOf, tcap] using h

/-- The rejected outcome: the machine at XF, every live cell still representing the start word memory m. -/
def AtFaultX (P : Program) (L : Lay3) (XF : W) (m : WMem) (s : Cpu) : Prop :=
  ∃ n v, runP P n s = v ∧ v.stopped = false ∧ v.rip = XF ∧ VIRBridge.Rep m v.mem L.live

set_option maxHeartbeats 1000000 in
/-- **compile_entry (NE-T).** The eager entry check for an EXTERNAL caller without a proof (OBJECT-NOCHECK-ENTRY; errata E1, E2). The
caller's state is `AtHead` at H with the capability (p₀, n₀) in ENV; H holds `call base_d` and the gate; H₂ holds `call base_e`. The
decider d (type cap × bool, READ-ONLY word code, compiled CHECKED at base_d) is SOUND: every finishing run leaves σ, returns the
capability it was given, and its bool true gives NC-P′ for e. e is compiled UNCHECKED at base_e. No `P σ` and no `NoFaultP` premise:
(F) a FAULTING run of d: the machine reaches XF with memory representing m;
(D) a FINISHING run of d with bool b: if b is false, XF with memory representing m; if true, XF the same way (d's OVF or RES), or the
    machine reaches e's code base in DriverCall and from there e's run is matched as `compile_x86_provedS` states it. -/
theorem compile_entry {lay : Int → W} {σ : Store} {m : WMem} {p₀ : Int} {n₀ : Nat}
    (d e : Tm₂) (τ : Ty₂)
    (hdty : HasType₂ [tcap] [true] d (.prod tcap tbool)) (hdw : Tm.wfB 1 d = true) (hdf : Tm.fnOk d = true)
    (hdok : Tm.ok2 d = true) (hdT : (lower2T [tcap] d []).2.length < 2 ^ 64)
    (hdro : ReadOnlyW (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 = true)
    (hety : HasType₂ [tcap] [true] e τ) (hew : Tm.wfB 1 e = true) (hef : Tm.fnOk e = true)
    (heok : Tm.ok2 e = true) (heT : (lower2T [tcap] e []).2.length < 2 ^ 64)
    (hR0 : σ.R.lookup p₀ = some n₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsound : ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ ∃ b, valOf w = Val.pair (Val.const (.cap p₀)) (Val.const (.bool b)) ∧
        (b = true → NoFaultP [(Atom.const (.cap p₀) : Atom₂)] e σ))
    {ilen : X86.Op → Nat} {based basee H H₂ XF : W} {Cd Ce : Ctx3} {P : Program} {L : Lay3}
    (hCd : Cd = ctxOfB true ilen (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 based)
    (hsubd : ∀ a i, (lower3B true ilen (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 based).at? a = some i → P.at? a = some i)
    (hCe : Ce = ctxOfU ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 basee)
    (hsube : ∀ a i, (lower3u ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 basee).at? a = some i → P.at? a = some i)
    (hC : ∀ o, 1 ≤ ilen o)
    (hbd : bytes Cd (allCode Cd (lower2T [tcap] d []).2 (lower2T [tcap] d []).1) < 2 ^ 64)
    (hbe : bytes Ce (allCode Ce (lower2T [tcap] e []).2 (lower2T [tcap] e []).1) < 2 ^ 64)
    (hNmd : needW (lower2T [tcap] d []).1 ≤ L.bufN) (hNtd : ∀ x ∈ (lower2T [tcap] d []).2, needW x.2 ≤ L.bufN)
    (hNme : needW (lower2T [tcap] e []).1 ≤ L.bufN) (hNte : ∀ x ∈ (lower2T [tcap] e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true)
    (hretd : canonical (H + 5) = true) (hrete : canonical (H₂ + 5) = true)
    (hcodeH : CodeAt Cd P H (.callA based :: gateTail L.env0 XF H₂)) (hcodeH₂ : CodeAt Ce P H₂ [.callA basee])
    (hbased : canonical based = true) (hbasee : canonical basee = true) (hX : canonical XF = true) (hH₂ : canonical H₂ = true)
    (hN : 3 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a)
    {s : Cpu} (hA : AtHead L H [lay p₀, BitVec.ofNat 64 n₀] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) S → Faults S → AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      AtFaultX P L XF m s ∨
      (valOf w = Val.pair (Val.const (.cap p₀)) (Val.const (.bool true)) ∧ ∃ n₁,
        DriverCall (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) [lay p₀, BitVec.ofNat 64 n₀] m
          (runP P n₁ s) ∧ (runP P n₁ s).rip = basee)) := by
  set Ld := L.reRet (H + 5) (based + BitVec.ofNat 64 (bytes Cd (stubHead Cd))) with hLd
  have hAd : AtHead Ld H [lay p₀, BitVec.ofNat 64 n₀] m s := reRet_atHead _ _ hA
  have hc0 : CodeAt Cd P s.rip (.callA based :: gateTail L.env0 XF H₂) := by rw [hA.rip]; exact hcodeH
  obtain ⟨hD1, hrip1⟩ := head_call (C := Cd) (reRet_ok hL _ _) hAd hc0 hbased rfl
  have hgate : CodeAt Cd P (H + 5) (gateTail L.env0 XF H₂) := by
    have := codeAt_right (a := [.callA based]) (b := gateTail L.env0 XF H₂) (by simpa using hcodeH)
    simpa [bytes_cons, bytes_nil, AI.size] using this
  have hdx := compile_x86S [tcap] [true] d (.prod tcap tbool) [.const (.cap p₀)] _ hdty hdw hdf hdok rfl (good_cap1 p₀) hdT
    (envRel_cap hR0) hl hm (L := Ld) hCd hsubd hC hbd hNmd hNtd (reRet_ok hL _ _)
    (fun a i h => hcanon a i h) hretd rfl hD1 hrip1 hlive
  obtain ⟨c1, c2, -⟩ := hdx
  -- every non-accept outcome: a Returned state with status ≠ 0 or BUF[2] ≠ 1, at a word memory reached from the start
  have reject : ∀ (mm : Nat) (code : W) (wm' : WMem), Returned Ld code (runP P (1 + mm) s) → Common Ld wm' (runP P (1 + mm) s) →
      wm' = m → (code ≠ 0 ∨ rd (runP P (1 + mm) s).mem (L.buf + 16) ≠ 1) → AtFaultX P L XF m s := by
    intro mm code wm' hRt hcm hwm hrej
    have hcu : CodeAt Cd P (runP P (1 + mm) s).rip (gateTail Ld.env0 XF H₂) := by rw [hRt.2.1]; exact hgate
    obtain ⟨n, v, hv, hvs, hvrip, hvm⟩ := gate_reject hRt hcm hcu hX hrej
    refine ⟨1 + mm + n, v, by rw [runP_add, hv], hvs, hvrip, ?_⟩
    rw [hvm, ← hwm]; exact hcm.2.2.2
  have r1 : ∀ mm, runP P mm (stepP P s) = runP P (1 + mm) s := fun mm => by rw [runP_add]; rfl
  have sF : stFault ≠ 0 := by decide
  have sO : stOvf ≠ 0 := by decide
  have sR : stRes ≠ 0 := by decide
  refine ⟨fun S hs hF => ?_, fun a σ' w hs hw' => ?_⟩
  · obtain ⟨mm, ⟨W', ⟨k, hk⟩, hR3, hW⟩ | ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩ := c2 S hs hF
    · obtain ⟨wst, wm'⟩ := W'
      have hwm : wm' = m := readOnly_mem hdro hk
      simp only at hW
      rcases hW with rfl | rfl
      · obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm (.inl sF)
      · obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm (.inl sO)
    · rw [r1] at hres hcm
      have hwm : Wr'.2 = m := readOnly_mem hdro (WN.trans hj (.step hst (.refl _)))
      exact reject mm _ _ hres hcm hwm (.inl sR)
  · obtain ⟨mm, ⟨W', ⟨k, hk⟩, hR3, hW⟩ | ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩ := c1 a σ' w hs hw'
    · obtain ⟨hσ, b, hv, hb⟩ := hsound a σ' w hs hw'
      obtain ⟨wst, wm'⟩ := W'
      have hwm : wm' = m := readOnly_mem hdro hk
      rcases hW with ⟨ws, m', hWe, hVR⟩ | h
      · simp only [Prod.mk.injEq] at hWe
        obtain ⟨rfl, rfl⟩ := hWe
        obtain ⟨hRt, hcm, -, hbuf⟩ := hR3
        rw [r1] at hRt hcm hbuf
        rw [hv, hσ] at hVR
        cases hVR with
        | pair h1 h2 =>
          cases h1 with
          | cap hRp =>
            cases h2 with
            | bool =>
              rw [hR0, Option.some.injEq] at hRp
              subst hRp
              cases b with
              | false =>
                left
                refine reject mm stDone wm' hRt hcm hwm (.inr ?_)
                have h0 : (runP P (1 + mm) s).mem.readN (L.buf + 16) 8 = 0 := by
                  have h := hbuf 2 (by simp); simpa [hLd, Lay3.reRet, boolW] using h
                simp only [rd]; rw [h0]; decide
              | true =>
                right
                refine ⟨hv, ?_⟩
                have hbuf' : WordsAt (runP P (1 + mm) s).mem Ld.buf [lay p₀, BitVec.ofNat 64 n₀, 1] := by
                  simpa [boolW] using hbuf
                have hcu : CodeAt Cd P (runP P (1 + mm) s).rip (gateTail Ld.env0 XF H₂) := by rw [hRt.2.1]; exact hgate
                obtain ⟨w', hw'', hA'⟩ := gate_accept (reRet_ok hL _ _) hRt hcm hbuf' hcu hX hH₂ (show 2 ≤ L.bufN by omega) hE hstk
                rw [hwm] at hA'
                have hAe : AtHead (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) H₂
                    [lay p₀, BitVec.ofNat 64 n₀] m w' :=
                  ⟨hA'.1, hA'.2, hA'.3, hA'.4, hA'.5, hA'.6, hA'.7, hA'.8, hA'.9, hA'.10, hA'.11, hA'.12⟩
                have hce : CodeAt Ce P w'.rip [.callA basee] := by rw [hA'.rip]; exact hcodeH₂
                obtain ⟨hD2, hrip2⟩ := head_call (C := Ce) (reRet_ok hL _ _) hAe hce hbasee rfl
                refine ⟨1 + mm + 14 + 1, ?_, ?_⟩
                · rw [runP_add, runP_add, hw'']; exact hD2
                · rw [runP_add, runP_add, hw'']; exact hrip2
      · left
        simp only at h; subst h
        obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm (.inl sO)
    · left
      rw [r1] at hres hcm
      have hwm : Wr'.2 = m := readOnly_mem hdro (WN.trans hj (.step hst (.refl _)))
      exact reject mm _ _ hres hcm hwm (.inl sR)


set_option maxHeartbeats 1000000 in
/-- **compile_entry_run (NE-T, whole).** `compile_entry` with its ACCEPT branch carried through e's run: from the DriverCall it reaches,
e's finishing runs and n-step prefixes are matched exactly as `compile_x86_provedS` states them (at the re-pointed layout). -/
theorem compile_entry_run {lay : Int → W} {σ : Store} {m : WMem} {p₀ : Int} {n₀ : Nat}
    (d e : Tm₂) (τ : Ty₂)
    (hdty : HasType₂ [tcap] [true] d (.prod tcap tbool)) (hdw : Tm.wfB 1 d = true) (hdf : Tm.fnOk d = true)
    (hdok : Tm.ok2 d = true) (hdT : (lower2T [tcap] d []).2.length < 2 ^ 64)
    (hdro : ReadOnlyW (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 = true)
    (hety : HasType₂ [tcap] [true] e τ) (hew : Tm.wfB 1 e = true) (hef : Tm.fnOk e = true)
    (heok : Tm.ok2 e = true) (heT : (lower2T [tcap] e []).2.length < 2 ^ 64)
    (hR0 : σ.R.lookup p₀ = some n₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsound : ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ ∃ b, valOf w = Val.pair (Val.const (.cap p₀)) (Val.const (.bool b)) ∧
        (b = true → NoFaultP [(Atom.const (.cap p₀) : Atom₂)] e σ))
    {ilen : X86.Op → Nat} {based basee H H₂ XF : W} {Cd Ce : Ctx3} {P : Program} {L : Lay3}
    (hCd : Cd = ctxOfB true ilen (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 based)
    (hsubd : ∀ a i, (lower3B true ilen (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 based).at? a = some i → P.at? a = some i)
    (hCe : Ce = ctxOfU ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 basee)
    (hsube : ∀ a i, (lower3u ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 basee).at? a = some i → P.at? a = some i)
    (hC : ∀ o, 1 ≤ ilen o)
    (hbd : bytes Cd (allCode Cd (lower2T [tcap] d []).2 (lower2T [tcap] d []).1) < 2 ^ 64)
    (hbe : bytes Ce (allCode Ce (lower2T [tcap] e []).2 (lower2T [tcap] e []).1) < 2 ^ 64)
    (hNmd : needW (lower2T [tcap] d []).1 ≤ L.bufN) (hNtd : ∀ x ∈ (lower2T [tcap] d []).2, needW x.2 ≤ L.bufN)
    (hNme : needW (lower2T [tcap] e []).1 ≤ L.bufN) (hNte : ∀ x ∈ (lower2T [tcap] e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true)
    (hretd : canonical (H + 5) = true) (hrete : canonical (H₂ + 5) = true)
    (hcodeH : CodeAt Cd P H (.callA based :: gateTail L.env0 XF H₂)) (hcodeH₂ : CodeAt Ce P H₂ [.callA basee])
    (hbased : canonical based = true) (hbasee : canonical basee = true) (hX : canonical XF = true) (hH₂ : canonical H₂ = true)
    (hN : 3 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a)
    {s : Cpu} (hA : AtHead L H [lay p₀, BitVec.ofNat 64 n₀] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) S → Faults S → AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      AtFaultX P L XF m s ∨
      (valOf w = Val.pair (Val.const (.cap p₀)) (Val.const (.bool true)) ∧ ∃ n₁,
        (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] e, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
              (∃ W', R3 Ce P (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) W' (runP P mm (runP P n₁ s)) ∧
                ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T [tcap] e []).2 lay σ' τ (valOf w) ws) ∨ W'.1 = .ovf)) ∨
              (∃ j Wr, WN (lower2T [tcap] e []).2 j (.run (lower2T [tcap] e []).1 [lay p₀, BitVec.ofNat 64 n₀] [], m) Wr ∧ ResWhy (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) Wr.1 ∧
                ResExit (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) (runP P mm (runP P n₁ s)))) ∧
            (∀ n S, SrcN n (instL 0 [(Atom.const (.cap p₀) : Atom₂)] e, σ) S → ∃ mm,
              (∃ W', R3 Ce P (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) W' (runP P mm (runP P n₁ s)) ∧ (n ≤ mm ∨ W'.1 = .ovf)) ∨
              (∃ j Wr, WN (lower2T [tcap] e []).2 j (.run (lower2T [tcap] e []).1 [lay p₀, BitVec.ofNat 64 n₀] [], m) Wr ∧ ResWhy (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) Wr.1 ∧
                ResExit (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) (runP P mm (runP P n₁ s)))))) := by
  obtain ⟨hF, hD⟩ := compile_entry d e τ hdty hdw hdf hdok hdT hdro hety hew hef heok heT hR0 hl hm hsound hCd hsubd hCe hsube hC
    hbd hbe hNmd hNtd hNme hNte hL hcanon hretd hrete hcodeH hcodeH₂ hbased hbasee hX hH₂ hN hE hstk hlive hA
  refine ⟨hF, fun a σ' w hs hw' => ?_⟩
  rcases hD a σ' w hs hw' with h | ⟨hv, n₁, hD2, hrip2⟩
  · exact .inl h
  · obtain ⟨-, b, hv', hb⟩ := hsound a σ' w hs hw'
    have hbt : b = true := by rw [hv] at hv'; cases hv'; rfl
    refine .inr ⟨hv, n₁, ?_⟩
    exact compile_x86_provedS [tcap] [true] e τ [.const (.cap p₀)] _ hety hew hef heok rfl (good_cap1 p₀) heT
      (envRel_cap hR0) hl hm (L := L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) hCe hsube hC hbe hNme hNte
      (reRet_ok hL _ _) hcanon hrete rfl hD2 hrip2 hlive (hb hbt)

end S3
