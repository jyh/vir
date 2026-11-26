/-
  O95, OBJECT-NOCHECK-ENTRY (amend-27; errata E1, E2, E3), route file 3: the entry stub. After the decider's code returns to ret0,
  Driver3's `loopTail env0 XF H₂` alone (status test: DONE goes on, anything else to XF; BUF[0..1] → ENV; jump to H₂), and at H₂
  `call base_e`. By E3 the decider has type `tcap` (L2 is linear in capabilities) and rejects by a deliberate index fault, which its
  CHECKED lowering turns into the FAULT status. E2's bool test (`boolChk`, `bool_check`, `gate_accept`, `gate_reject`) and E2's
  `compile_entry` were proved at 55962a3 for an interface no L2 program instantiates; they are removed here and 55962a3 is their record.
  A new file (NE4).
-/
import S3.Driver3
import S3.Contain
import S3.ReadOnly

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- A layout with its return point re-pointed (`Lay3.Ok`, `Common`, `AtHead` and `DriverCall` other than `ret` do not read `ret0`). -/
def Lay3.reRet (L : Lay3) (r s : W) : Lay3 := { L with ret0 := r, stubRet := s }

theorem reRet_ok {L : Lay3} (hL : L.Ok) (r s : W) : (L.reRet r s).Ok := by
  cases hL; constructor <;> assumption

theorem reRet_common {L : Lay3} {wm : WMem} {u : Cpu} (r s : W) (h : Common L wm u) : Common (L.reRet r s) wm u := h

theorem reRet_atHead {L : Lay3} {H : W} {ρ : List W} {wm : WMem} {u : Cpu} (r s : W) (h : AtHead L H ρ wm u) :
    AtHead (L.reRet r s) H ρ wm u := ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12⟩

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
/-- **compile_entry (NE-T).** The eager entry check for an EXTERNAL caller without a proof (OBJECT-NOCHECK-ENTRY; errata E1–E3). The
caller's state is `AtHead` at H with the capability (p₀, n₀) in ENV; H holds `call base_d` and `loopTail`; H₂ holds `call base_e`. The
decider d (type tcap, READ-ONLY word code, compiled CHECKED at base_d) is SOUND: every finishing run leaves σ, returns the capability it
was given, and gives NC-P′ for e (a decider rejects by faulting, so finishing IS accepting). e is compiled UNCHECKED at base_e. No `P σ`
and no `NoFaultP` premise:
(F) a FAULTING run of d: the machine reaches XF with memory representing m;
(D) a FINISHING run of d: XF the same way (d's OVF or RES), or the machine reaches e's code base in DriverCall. -/
theorem compile_entry {lay : Int → W} {σ : Store} {m : WMem} {p₀ : Int} {n₀ : Nat}
    (d e : Tm₂) (τ : Ty₂)
    (hdty : HasType₂ [tcap] [true] d tcap) (hdw : Tm.wfB 1 d = true) (hdf : Tm.fnOk d = true)
    (hdok : Tm.ok2 d = true) (hdT : (lower2T [tcap] d []).2.length < 2 ^ 64)
    (hdro : ReadOnlyW (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 = true)
    (hety : HasType₂ [tcap] [true] e τ) (hew : Tm.wfB 1 e = true) (hef : Tm.fnOk e = true)
    (heok : Tm.ok2 e = true) (heT : (lower2T [tcap] e []).2.length < 2 ^ 64)
    (hR0 : σ.R.lookup p₀ = some n₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsound : ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ valOf w = Val.const (.cap p₀) ∧ NoFaultP [(Atom.const (.cap p₀) : Atom₂)] e σ)
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
    (hcodeH : CodeAt Cd P H (.callA based :: loopTail L.env0 XF H₂)) (hcodeH₂ : CodeAt Ce P H₂ [.callA basee])
    (hbased : canonical based = true) (hbasee : canonical basee = true) (hX : canonical XF = true) (hH₂ : canonical H₂ = true)
    (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a)
    {s : Cpu} (hA : AtHead L H [lay p₀, BitVec.ofNat 64 n₀] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) S → Faults S → AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      AtFaultX P L XF m s ∨
      (∃ n₁,
        DriverCall (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) [lay p₀, BitVec.ofNat 64 n₀] m
          (runP P n₁ s) ∧ (runP P n₁ s).rip = basee)) := by
  set Ld := L.reRet (H + 5) (based + BitVec.ofNat 64 (bytes Cd (stubHead Cd))) with hLd
  have hAd : AtHead Ld H [lay p₀, BitVec.ofNat 64 n₀] m s := reRet_atHead _ _ hA
  have hc0 : CodeAt Cd P s.rip (.callA based :: loopTail L.env0 XF H₂) := by rw [hA.rip]; exact hcodeH
  obtain ⟨hD1, hrip1⟩ := head_call (C := Cd) (reRet_ok hL _ _) hAd hc0 hbased rfl
  have hgate : CodeAt Cd P (H + 5) (loopTail L.env0 XF H₂) := by
    have := codeAt_right (a := [.callA based]) (b := loopTail L.env0 XF H₂) (by simpa using hcodeH)
    simpa [bytes_cons, bytes_nil, AI.size] using this
  have hdx := compile_x86S [tcap] [true] d tcap [.const (.cap p₀)] _ hdty hdw hdf hdok rfl (good_cap1 p₀) hdT
    (envRel_cap hR0) hl hm (L := Ld) hCd hsubd hC hbd hNmd hNtd (reRet_ok hL _ _)
    (fun a i h => hcanon a i h) hretd rfl hD1 hrip1 hlive
  obtain ⟨c1, c2, -⟩ := hdx
  -- every non-accept outcome: a Returned state with status ≠ 0, at a word memory reached from the start
  have reject : ∀ (mm : Nat) (code : W) (wm' : WMem), Returned Ld code (runP P (1 + mm) s) → Common Ld wm' (runP P (1 + mm) s) →
      wm' = m → code ≠ 0 → AtFaultX P L XF m s := by
    intro mm code wm' hRt hcm hwm hne
    have hcu : CodeAt Cd P (runP P (1 + mm) s).rip (loopTail Ld.env0 XF H₂) := by rw [hRt.2.1]; exact hgate
    obtain ⟨x, hx, hxs, hxm, -, hxrip⟩ := loop_check hRt.1 hcu hcm hX
    rw [if_neg (by rw [hRt.2.2.2]; exact hne)] at hxrip
    refine ⟨1 + mm + 4, x, by rw [runP_add, hx], hxs, hxrip, ?_⟩
    rw [hxm, ← hwm]; exact hcm.2.2.2
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
      · obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm sF
      · obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm sO
    · rw [r1] at hres hcm
      have hwm : Wr'.2 = m := readOnly_mem hdro (WN.trans hj (.step hst (.refl _)))
      exact reject mm _ _ hres hcm hwm sR
  · obtain ⟨mm, ⟨W', ⟨k, hk⟩, hR3, hW⟩ | ⟨j, Wr, Wr', hj, hst, hres, hcm⟩⟩ := c1 a σ' w hs hw'
    · obtain ⟨hσ, hv, -⟩ := hsound a σ' w hs hw'
      obtain ⟨wst, wm'⟩ := W'
      have hwm : wm' = m := readOnly_mem hdro hk
      rcases hW with ⟨ws, m', hWe, hVR⟩ | h
      · simp only [Prod.mk.injEq] at hWe
        obtain ⟨rfl, rfl⟩ := hWe
        obtain ⟨hRt, hcm, -, hbuf⟩ := hR3
        rw [r1] at hRt hcm hbuf
        rw [hv, hσ] at hVR
        cases hVR with
        | cap hRp =>
          rw [hR0, Option.some.injEq] at hRp
          subst hRp
          right
          have hcu : CodeAt Cd P (runP P (1 + mm) s).rip (loopTail Ld.env0 XF H₂) := by rw [hRt.2.1]; exact hgate
          obtain ⟨w', hw'', hA'⟩ := after_done (reRet_ok hL _ _) hRt hcm hbuf hcu hX hH₂ hN hE hstk
          rw [hwm] at hA'
          have hAe : AtHead (L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) H₂
              [lay p₀, BitVec.ofNat 64 n₀] m w' :=
            ⟨hA'.1, hA'.2, hA'.3, hA'.4, hA'.5, hA'.6, hA'.7, hA'.8, hA'.9, hA'.10, hA'.11, hA'.12⟩
          have hce : CodeAt Ce P w'.rip [.callA basee] := by rw [hA'.rip]; exact hcodeH₂
          obtain ⟨hD2, hrip2⟩ := head_call (C := Ce) (reRet_ok hL _ _) hAe hce hbasee rfl
          refine ⟨1 + mm + 10 + 1, ?_, ?_⟩
          · rw [runP_add, runP_add, hw'']; exact hD2
          · rw [runP_add, runP_add, hw'']; exact hrip2
      · left
        simp only at h; subst h
        obtain ⟨hRt, hcm⟩ := hR3; rw [r1] at hRt hcm; exact reject mm _ wm' hRt hcm hwm sO
    · left
      rw [r1] at hres hcm
      have hwm : Wr'.2 = m := readOnly_mem hdro (WN.trans hj (.step hst (.refl _)))
      exact reject mm _ _ hres hcm hwm sR


set_option maxHeartbeats 1000000 in
/-- **compile_entry_run (NE-T, whole).** `compile_entry` with its ACCEPT branch carried through e's run: from the DriverCall it reaches,
e's finishing runs and n-step prefixes are matched exactly as `compile_x86_provedS` states them (at the re-pointed layout). -/
theorem compile_entry_run {lay : Int → W} {σ : Store} {m : WMem} {p₀ : Int} {n₀ : Nat}
    (d e : Tm₂) (τ : Ty₂)
    (hdty : HasType₂ [tcap] [true] d tcap) (hdw : Tm.wfB 1 d = true) (hdf : Tm.fnOk d = true)
    (hdok : Tm.ok2 d = true) (hdT : (lower2T [tcap] d []).2.length < 2 ^ 64)
    (hdro : ReadOnlyW (lower2T [tcap] d []).2 (lower2T [tcap] d []).1 = true)
    (hety : HasType₂ [tcap] [true] e τ) (hew : Tm.wfB 1 e = true) (hef : Tm.fnOk e = true)
    (heok : Tm.ok2 e = true) (heT : (lower2T [tcap] e []).2.length < 2 ^ 64)
    (hR0 : σ.R.lookup p₀ = some n₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsound : ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ valOf w = Val.const (.cap p₀) ∧ NoFaultP [(Atom.const (.cap p₀) : Atom₂)] e σ)
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
    (hcodeH : CodeAt Cd P H (.callA based :: loopTail L.env0 XF H₂)) (hcodeH₂ : CodeAt Ce P H₂ [.callA basee])
    (hbased : canonical based = true) (hbasee : canonical basee = true) (hX : canonical XF = true) (hH₂ : canonical H₂ = true)
    (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a)
    {s : Cpu} (hA : AtHead L H [lay p₀, BitVec.ofNat 64 n₀] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) S → Faults S → AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] d, σ) (.ret a, σ') → Atom.eval a = some w →
      AtFaultX P L XF m s ∨
      (∃ n₁,
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
  rcases hD a σ' w hs hw' with h | ⟨n₁, hD2, hrip2⟩
  · exact .inl h
  · obtain ⟨-, -, hb⟩ := hsound a σ' w hs hw'
    refine .inr ⟨n₁, ?_⟩
    exact compile_x86_provedS [tcap] [true] e τ [.const (.cap p₀)] _ hety hew hef heok rfl (good_cap1 p₀) heT
      (envRel_cap hR0) hl hm (L := L.reRet (H₂ + 5) (basee + BitVec.ofNat 64 (bytes Ce (stubHead Ce)))) hCe hsube hC hbe hNme hNte
      (reRet_ok hL _ _) hcanon hrete rfl hD2 hrip2 hlive hb

end S3
