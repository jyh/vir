/-
  O95 option (iv), OBJECT-NOCHECK NC-S: `compile_x86_proved`, the compiler from the SOURCE to x86-64 for a PROVED program, through
  the UNCHECKED lowering `lower3u` (no index check instructions, NC-L). compile_x86's premises with `lower3u`/`ctxOfU` in place of
  `lower3`/`ctxOf`, plus NC-P′ (`NoFaultP`, ERRATA-NOCHECK E1); its conclusion is compile_x86's clauses (1) and (3), with no FAULT
  clause. NC-W (`word_no_fault`) supplies S3's no-FAULT premise; nothing in compiler/VIRC is edited.
-/
import S3.Cross3
import S3.NoFault

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- The unchecked layout: `ctxOfB false`. -/
def ctxOfU (ilen : X86.Op → Nat) (tbl : Table) (main : WCode) (base : W) : Ctx3 := ctxOfB false ilen tbl main base

/-- **lift3u.** `lift3` for the unchecked lowering: S3's premises for `lower3u`, S2's SRel at main's start, and no reached word state
    FAULT (`hnf`), give the same two outcomes. -/
theorem lift3u {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    {lay : Int → W} {τfin : VIRL2.Ty₂} {I₀ : St × VIRL2.Store}
    (hCdef : C = ctxOfU ilen tbl main base) (hp : p = lower3u ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
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
    s3_refines_from_s2B (b := false) hCdef hp hC hb hT64 hNm hNt hL hcanon hretc hstub hD hrip h0 hlive (fun _ => hnf) hrun
  · exact ⟨m, .inl h⟩
  · exact ⟨m, .inr ⟨j, Wr, hj, hwhy, hres⟩⟩

/-- **compile_x86_proved (NC-S).** For a program e accepted by S1 ∘ S2 under compile_x86's premises, lowered by `lower3u` (no index
checks) at `base` under the layout `ctxOfU`, and PROVED in the sense of NC-P′ (`NoFaultP vs e σ`: no reachable source configuration
faults and every reached `ret` atom evaluates; every L2 `Triple` supplies it), every clause ends in a machine state after mm `stepP`
steps that is R3-related to a word state W', or in RES at a reached word state whose `ResWhy` holds:
(1) a ⟶₂ run that FINISHES with `ret a`, a evaluating to w: W' is `done ws` with ws related to w's IR image, or W' is OVF;
(3) n ⟶₂ steps: mm ≥ n, or W' is OVF.
compile_x86's clause (2) (a FAULTING run) is absent: under NC-P′ there is none. -/
theorem compile_x86_proved {lay : Int → W} {σ : VIRL2.Store} {m : WMem} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂)
    (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfU ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base)
    (hp : p = lower3u ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base) (hC : ∀ o, 1 ≤ ilen o)
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
    lift3u (I₀ := (.run (lowerT e) (vs.map valOf) [], σ)) hCdef hp hC hb hT hNm hNt hL hcanon hretc hstub hD hrip h0 hlive
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
