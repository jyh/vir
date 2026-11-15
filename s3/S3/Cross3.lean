/-
  O95 compiler, the cross-stage statement (compiler/DECLARATIONS-S3.md, Addendum 15). S1 ∘ S2 (`VIRC.compile_refines`, a statement
  about the SOURCE program) composed with S3 (`s3_refines_from_s2`), from `s2_init`'s SRel at main's start. No premise beyond the
  union of the two stages' premises; nothing in S1, S2 or S3 is edited.
-/
import S3.Sem3
import VIRC.Compose

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- **lift3.** Under S3's premises and S2's SRel at main's start, a k-step word run from that start is matched by a machine run
    of at least k + 3 steps ending R3-related to the reached word state, or by RES at some reached word state whose `ResWhy`
    holds. (A restatement of `s3_refines_from_s2` whose RES side keeps only what the cross-stage statement reads.) -/
theorem lift3 {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    {lay : Int → W} {τfin : VIRL2.Ty₂} {I₀ : St × VIRL2.Store}
    (hCdef : C = ctxOf ilen tbl main base) (hp : p = lower3 ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    (h0 : SRel tbl lay τfin I₀ (.run main ρ₀ [], wm)) (hlive : ∀ a, VIRBridge.Live I₀.2 lay a → L.live a)
    {k : Nat} {Wf : WSt × WMem} (hrun : WN tbl k (.run main ρ₀ [], wm) Wf) :
    ∃ m, (k + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ j Wr, WN tbl j (.run main ρ₀ [], wm) Wr ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s)) := by
  obtain ⟨m, h | ⟨Wr, -, j, hj, -, hwhy, hres, -⟩⟩ :=
    s3_refines_from_s2 hCdef hp hC hb hT64 hNm hNt hL hcanon hretc hstub hD hrip h0 hlive hrun
  · exact ⟨m, .inl h⟩
  · exact ⟨m, .inr ⟨j, Wr, hj, hwhy, hres⟩⟩

/-- **compile_x86, the compiler from the SOURCE to x86-64.** For a program e accepted by S1 ∘ S2 (typed under Γ₀, closed below it,
C2 and S2's predicate, caller values vs related to the caller words ρw₀, table under 2⁶⁴ entries, `Layout`, `MemRel`), lowered by
`lower3` at `base` under S3's premises (layout, canonical addresses, the stub's return point, `DriverCall` on ρw₀, Fragment3's
static clauses, and L.live covering σ's live cells), every clause ends in a machine state after mm `stepP` steps that is R3-related
to a word state W', or in RES at a reached word state whose `ResWhy` holds (ENV or STACK outgrown):
(1) a ⟶₂ run that FINISHES with `ret a`, a evaluating to w: W' is `done ws` with ws related to w's IR image (R3 there: returned
    with stDone, r13 = |ws|, the words at BUF), or W' is OVF;
(2) a ⟶₂ run that FAULTS: W' is FAULT or OVF;
(3) n ⟶₂ steps: mm ≥ n, or W' is OVF. -/
theorem compile_x86 {lay : Int → W} {σ : VIRL2.Store} {m : WMem} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂)
    (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOf ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base)
    (hp : p = lower3 ilen (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T Γ₀ e []).2 (lower2T Γ₀ e []).1) < 2 ^ 64)
    (hNm : needW (lower2T Γ₀ e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T Γ₀ e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {s : Cpu} (hD : DriverCall L ρw₀ m s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) :
    (∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧ ResWhy L Wr.1 ∧
        ResExit L (runP p mm s))) ∧
    (∀ S, Steps₂ (instL 0 vs e, σ) S → Faults S → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧ ResWhy L Wr.1 ∧
        ResExit L (runP p mm s))) ∧
    (∀ n S, SrcN n (instL 0 vs e, σ) S → ∃ mm,
      (∃ W', R3 C p L W' (runP p mm s) ∧ (n ≤ mm ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T Γ₀ e []).2 j (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wr ∧ ResWhy L Wr.1 ∧
        ResExit L (runP p mm s))) := by
  have h0 := s2_init Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok he hl hm
  have lift := fun {k} {Wf} (hrun : WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wf) =>
    lift3 (I₀ := (.run (lowerT e) (vs.map valOf) [], σ)) hCdef hp hC hb hT hNm hNt hL hcanon hretc hstub hD hrip h0 hlive hrun
  obtain ⟨c1, c2, c3⟩ := compile_refines Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm
  refine ⟨fun a σ' w hs hw' => ?_, fun S hs hF => ?_, fun n S hn => ?_⟩
  · obtain ⟨k, W', hW, hP⟩ := c1 a σ' w hs hw'
    obtain ⟨mm, ⟨-, hR⟩ | hr⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hP⟩⟩
    · exact ⟨mm, .inr hr⟩
  · obtain ⟨k, W', hW, hP⟩ := c2 S hs hF
    obtain ⟨mm, ⟨-, hR⟩ | hr⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hP⟩⟩
    · exact ⟨mm, .inr hr⟩
  · obtain ⟨k, W', hW, hP⟩ := c3 n S hn
    obtain ⟨mm, ⟨hk, hR⟩ | hr⟩ := lift hW
    · exact ⟨mm, .inl ⟨W', hR, hP.imp (fun h => by omega) id⟩⟩
    · exact ⟨mm, .inr hr⟩

end S3
