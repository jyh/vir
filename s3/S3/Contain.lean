/-
  O95, OBJECT-NOCHECK-ENTRY (amend-27), route file 1: the S3 chain for a program p that CONTAINS a lowering's code rather than
  equals it (`hsub`: p agrees with `lower3B b …` on every address the lowering defines). A new file; no existing S3 file is edited (NE4).
-/
import S3.Proved

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- CodeAt transfers to a program that agrees on the addresses. -/
theorem codeAt_sub {C : Ctx3} {p p' : Program} (hsub : ∀ a i, p.at? a = some i → p'.at? a = some i) {pc : W} {l : List AI}
    (h : CodeAt C p pc l) : CodeAt C p' pc l := fun j hj => hsub _ _ (h j hj)

/-- **lower3_placedS.** `lower3_placed` for a program that contains `lower3B bc`'s code. -/
theorem lower3_placedS {bc : Bool} {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program}
    (hCdef : C = ctxOfB bc ilen tbl main base) (hsub : ∀ a i, (lower3B bc ilen tbl main base).at? a = some i → p.at? a = some i)
    (hC : ∀ o, 1 ≤ ilen o) (hb : bytes C (allCode C tbl main) < 2 ^ 64) :
    CodeAt C p base (entryStub (mainAddr C)) ∧ CodeAt C p C.fault (exitCode stFault) ∧ CodeAt C p C.ovf (exitCode stOvf) ∧
      CodeAt C p C.res (exitCode stRes) ∧ CodeAt C p (mainAddr C) (gen C (mainAddr C) main) ∧
      (∀ i fx b, tbl[i]? = some (fx, b) → C.fix i = fx ∧ CodeAt C p (C.body i) (gen C (C.body i) b)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lower3_placed (p := lower3B bc ilen tbl main base) hCdef rfl hC hb
  exact ⟨codeAt_sub hsub h1, codeAt_sub hsub h2, codeAt_sub hsub h3, codeAt_sub hsub h4, codeAt_sub hsub h5,
    fun i fx b h => ⟨(h6 i fx b h).1, codeAt_sub hsub (h6 i fx b h).2⟩⟩

/-- **s3_refines_lower3S.** `s3_refines_lower3` for a program p that CONTAINS `lower3B bc`'s code (`hsub`). -/
theorem s3_refines_lower3S {bc : Bool} {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfB bc ilen tbl main base) (hsub : ∀ a i, (lower3B bc ilen tbl main base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf)
    (hok : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → StepOk L W₁.1)
    (hnf : C.chk = false → ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → W₁.1 ≠ .fault) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) := by
  obtain ⟨hst, hF, hO, hR, hM, hTb⟩ := lower3_placedS hCdef hsub hC hb
  have E : StepEnv C p L := ⟨hL, hcanon, hretc, hF, hO, hR⟩
  have hT : TblOk C p tbl := ⟨by subst hCdef; rfl, by subst hCdef; exact hT64, hTb⟩
  have hE : Entry C p L main ρ₀ wm s := ⟨hD.stopped, by rw [hrip]; exact hst, by rw [hrip]; exact hstub, hM, hD.r14, hD.rbx,
    hD.r12, hD.rsp, hD.ret, hD.cb16, hD.cb24, hD.rep, hD.words, hD.hi, hD.stk⟩
  exact s3_refines E hT hE hrun hok hnf

/-- **s3_refines_lower3_staticS.** `s3_refines_lower3_staticB` with `hsub` for `hp`. -/
theorem s3_refines_lower3_staticS {b : Bool} {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfB b ilen tbl main base) (hsub : ∀ a i, (lower3B b ilen tbl main base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf)
    (hsem : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → StepSem L W₁.1)
    (hnf : C.chk = false → ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → W₁.1 ≠ .fault) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) :=
  s3_refines_lower3S hCdef hsub hC hb hT64 hL hcanon hretc hstub hD hrip hrun
    (fun k W₁ hk => stepOk_of (needOk_run hNt hk ⟨hNm, by simp⟩) (hsem k W₁ hk)) hnf

/-- **s3_refines_from_s2S.** `s3_refines_from_s2B` with `hsub` for `hp`. -/
theorem s3_refines_from_s2S {b : Bool} {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    {lay : Int → W} {τfin : VIRL2.Ty₂} {I₀ : St × VIRL2.Store}
    (hCdef : C = ctxOfB b ilen tbl main base) (hsub : ∀ a i, (lower3B b ilen tbl main base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    (h0 : SRel tbl lay τfin I₀ (.run main ρ₀ [], wm)) (hlive : ∀ a, VIRBridge.Live I₀.2 lay a → L.live a)
    (hnf : C.chk = false → ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → W₁.1 ≠ .fault)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) := by
  refine s3_refines_lower3_staticS hCdef hsub hC hb hT64 hNm hNt hL hcanon hretc hstub hD hrip hrun ?_ hnf
  intro k W₁ hk
  rcases srel_reach_R hT64 hk h0 with ⟨I₁, h1, h2⟩ | ht
  · exact stepSem_of_srel hT64 h1 (fun a ha => hlive a (live_of_R h2 a ha))
  · obtain ⟨w, m⟩ := W₁
    rcases ht with ht | ht <;> (simp only at ht; subst ht; trivial)

/-- **lift3uS.** `lift3u` with `hsub` for `hp`. -/
theorem lift3uS {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    {lay : Int → W} {τfin : VIRL2.Ty₂} {I₀ : St × VIRL2.Store}
    (hCdef : C = ctxOfU ilen tbl main base) (hsub : ∀ a i, (lower3u ilen tbl main base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    (h0 : SRel tbl lay τfin I₀ (.run main ρ₀ [], wm)) (hlive : ∀ a, VIRBridge.Live I₀.2 lay a → L.live a)
    (hnf : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → W₁.1 ≠ .fault)
    {k : Nat} {Wf : WSt × WMem} (hrun : WN tbl k (.run main ρ₀ [], wm) Wf) :
    ∃ m, (k + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ j Wr, WN tbl j (.run main ρ₀ [], wm) Wr ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s)) := by
  obtain ⟨m, h | ⟨Wr, -, j, hj, -, hwhy, hres, -⟩⟩ :=
    s3_refines_from_s2S (b := false) hCdef hsub hC hb hT64 hNm hNt hL hcanon hretc hstub hD hrip h0 hlive (fun _ => hnf) hrun
  · exact ⟨m, .inl h⟩
  · exact ⟨m, .inr ⟨j, Wr, hj, hwhy, hres⟩⟩

/-- **compile_x86_provedS.** `compile_x86_proved` for a program p that CONTAINS `lower3u`'s code (`hsub`), so that e's code can sit
    beside other code (OBJECT-NOCHECK-ENTRY's entry stub and decider). -/
theorem compile_x86_provedS {lay : Int → W} {σ : VIRL2.Store} {m : WMem} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂)
    (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfU ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base)
    (hsub : ∀ a i, (lower3u ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base).at? a = some i → p.at? a = some i) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1) < 2 ^ 64)
    (hNm : needW (lower2T Γ₀ e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T Γ₀ e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {s : Cpu} (hD : DriverCall L ρw₀ m s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) (hP : NoFaultP vs e σ) :
    (∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧ ResWhy L Wr.1 ∧
        ResExit L (runP p mm s))) ∧
    (∀ n S, SrcN n (instL 0 vs e, σ) S → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧ (n ≤ mm ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧ ResWhy L Wr.1 ∧
        ResExit L (runP p mm s))) := by
  have h0 := s2_init Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok he hl hm
  have lift := fun {k} {Wf} (hrun : WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wf) =>
    lift3uS (I₀ := (.run (lowerT e) (vs.map valOf) [], σ)) hCdef hsub hC hb hT hNm hNt hL hcanon hretc hstub hD hrip h0 hlive
      (fun k W₁ hk => word_no_fault Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm hP hk) hrun
  obtain ⟨c1, -, c3⟩ := compile_refines Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm
  refine ⟨fun a σ' w hs hw' => ?_, fun n S hn => ?_⟩
  · obtain ⟨k, W', hW, hQ⟩ := c1 a σ' w hs hw'
    obtain ⟨mm, ⟨-, hR⟩ | hr⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hQ⟩⟩
    · exact ⟨mm, .inr hr⟩
  · obtain ⟨k, W', hW, hQ⟩ := c3 n S hn
    obtain ⟨mm, ⟨hk, hR⟩ | hr⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hQ.imp (fun h => by omega) id⟩⟩
    · exact ⟨mm, .inr hr⟩

end S3
