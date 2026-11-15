/-
  O95, **K7-b1** (compiler/DECLARATIONS-K7.md Addendum 1): the L3 router F through S1∘S2∘S3. `S3.compile_x86` at F, exactly as K7-a
  instantiates compile_refines (Γ₀ = [tcap], vs = [cap p], k5's generic scaled loader). Only evaluation facts and the one
  instantiation. The code-size premise (abstract `ilen`), S3's layout premises, and the OVF and RES disjuncts STAY.
-/
import K7.Router
import S3.Cross3

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

set_option maxRecDepth 100000 in
/-- F's BUF demand (main), read off by evaluation (k7-probe-need-001 printed 5). -/
theorem F_need : S3.needW (lower2T [tcap] F []).1 ≤ 5 := by decide
set_option maxRecDepth 100000 in
/-- F's lowered function table is empty (k7-probe-need-001 printed []). -/
theorem F_tbl_nil : (lower2T [tcap] F []).2 = [] := by decide

/-- **K7-b1.** For every WF world σ placed in [0, 2⁶⁰) with in-range cells and the router's capability region at p, and the router's
lowered code P = `lower3 ilen T main base` under S3's layout premises with |BUF| ≥ 5: compile_x86's three clauses for F. -/
theorem router_x86 {σ : Store} {p : Int} {n : Nat} (hR : σ.R.lookup p = some n) (hw : σ.WF) (hpl : Placed σ)
    (hc : CellsInR σ)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3}
    (hCdef : C = S3.ctxOf ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base)
    (hP : P = S3.lower3 ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : S3.bytes C (S3.allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hN : 5 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → X86.canonical a = true) (hretc : X86.canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (S3.bytes C (S3.stubHead C)))
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay p n) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a) :
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] F, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
      (∃ W', S3.R3 C P L W' (X86.runP P mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T [tcap] F []).2 scaleLay σ' tcap (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 (capWords scaleLay p n) [], scaleMem σ) Wr ∧
        S3.ResWhy L Wr.1 ∧ S3.ResExit L (X86.runP P mm s))) ∧
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] F, σ) S → Faults S → ∃ mm,
      (∃ W', S3.R3 C P L W' (X86.runP P mm s) ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 (capWords scaleLay p n) [], scaleMem σ) Wr ∧
        S3.ResWhy L Wr.1 ∧ S3.ResExit L (X86.runP P mm s))) ∧
    (∀ k S, SrcN k (instL 0 [(Atom.const (.cap p) : Atom₂)] F, σ) S → ∃ mm,
      (∃ W', S3.R3 C P L W' (X86.runP P mm s) ∧ (k ≤ mm ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 (capWords scaleLay p n) [], scaleMem σ) Wr ∧
        S3.ResWhy L Wr.1 ∧ S3.ResExit L (X86.runP P mm s))) := by
  obtain ⟨hl, hm⟩ := loader_ok hw hpl hc
  exact S3.compile_x86 [tcap] [true] F tcap [.const (.cap p)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap p) F_table
    (envRel_cap1 hR) hl hm hCdef hP hC hb (le_trans F_need hN) (by rw [F_tbl_nil]; intro x hx; cases hx) hL hcanon hretc
    hstub hD hrip hlive

end K7
