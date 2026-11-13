/-
  O95, **K7-a** (compiler/DECLARATIONS-K7.md): the L3 router F through S1∘S2. `compile_refines` at F (Γ₀ = [tcap], vs = [cap p]),
  with k5's generic scaled loader. Only evaluation facts and the one instantiation: no lemma about F's structure, layout or cells.
  The overflow disjunct stays (the router's own SrcInRange is not claimed).
-/
import VIRL3.Typing
import K5.Loader
import K5.DeflateNoOvf

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

set_option maxRecDepth 100000 in
theorem F_wfB : Tm.wfB [tcap].length F = true := by decide
set_option maxRecDepth 100000 in
theorem F_fnOk : Tm.fnOk F = true := by decide
set_option maxRecDepth 100000 in
theorem F_ok2 : Tm.ok2 F = true := by decide
set_option maxRecDepth 100000 in
theorem F_table : (lower2T [tcap] F []).2.length < 2 ^ 64 := by decide

/-- EnvRel for one cap parameter, at ANY table (generic: names no program). -/
theorem envRel_cap1 {T : Table} {lay : Int → W} {σ : Store} {p : Int} {L : Nat} (hR : σ.R.lookup p = some L) :
    EnvRel T lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) (capWords lay p L) := by
  have h := EnvRel.cons (T := T) (lay := lay) (Γ := []) (ρ := []) (ρw := []) (VRel.cap (T := T) (lay := lay) hR) .nil
  simpa [capWords, valOf, tcap] using h

/-- **K7-a.** For every WF world σ placed in [0, 2⁶⁰) with in-range cells and the router's capability region at p: compile_refines'
three clauses for the router F, compiled by S1∘S2, against the scaled loader's memory. -/
theorem router_refines {σ : Store} {p : Int} {n : Nat} (hR : σ.R.lookup p = some n) (hw : σ.WF) (hpl : Placed σ)
    (hc : CellsInR σ) :
    let T := (lower2T [tcap] F []).2
    let W₀ : WSt × WMem := (.run (lower2T [tcap] F []).1 (capWords scaleLay p n) [], scaleMem σ)
    let src : Tm₂ := instL 0 [(Atom.const (.cap p) : Atom₂)] F
    (∀ a σ' w, Steps₂ (src, σ) (.ret a, σ') → Atom.eval a = some w →
      ∃ k W', WN T k W₀ W' ∧ ((∃ ws m', W' = (.done ws, m') ∧ VRel T scaleLay σ' tcap (valOf w) ws) ∨ W'.1 = .ovf)) ∧
    (∀ S, Steps₂ (src, σ) S → Faults S → ∃ k W', WN T k W₀ W' ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∧
    (∀ m S, SrcN m (src, σ) S → ∃ k W', WN T k W₀ W' ∧ (m ≤ k ∨ W'.1 = .ovf)) := by
  obtain ⟨hl, hm⟩ := loader_ok hw hpl hc
  exact compile_refines [tcap] [true] F tcap [.const (.cap p)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap p) F_table
    (envRel_cap1 hR) hl hm

end K7
