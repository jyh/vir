/-
  O95, **K5-3 `deflate_noovf`** (compiler/DECLARATIONS-K5.md K5-3, Addendum 6) and row 296's instantiation of `compile_refines`
  at DEFLATE's step term. Γ₀ = [tcap], vs = [cap p], ρw₀ = the cap's two words. The four per-program facts close by evaluation;
  `Layout`/`MemRel` (the loader premise every program carries) stay hypotheses, and no layout lemma about DEFLATE is added (K6).
-/
import K5.DeflateInRange
import VIRDeflate.Typing

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

set_option maxRecDepth 100000 in
theorem stepT_wfB : Tm.wfB [tcap].length stepT = true := by decide
set_option maxRecDepth 100000 in
theorem stepT_fnOk : Tm.fnOk stepT = true := by decide
set_option maxRecDepth 100000 in
theorem stepT_ok2 : Tm.ok2 stepT = true := by decide
set_option maxRecDepth 100000 in
theorem stepT_table : (lower2T [tcap] stepT []).2.length < 2 ^ 64 := by decide

theorem stepT_inst (p : Int) : instL 0 [.const (.cap p)] stepT = closeAt p stepT := rfl

theorem good_cap (p : Int) : Good [.const (.cap p)] := by
  intro w hw
  simp only [List.mem_singleton] at hw
  subst hw
  exact ⟨rfl, rfl, rfl⟩

/-- The cap's two words. -/
def capWords (lay : Int → W) (p : Int) (L : Nat) : List W := [lay p, BitVec.ofNat 64 L]

theorem envRel_cap {lay : Int → W} {σ : Store} {p : Int} {L : Nat} (hR : σ.R.lookup p = some L) :
    EnvRel (lower2T [tcap] stepT []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) (capWords lay p L) := by
  have h := EnvRel.cons (T := (lower2T [tcap] stepT []).2) (lay := lay) (Γ := []) (ρ := []) (ρw := [])
    (VRel.cap (T := (lower2T [tcap] stepT []).2) (lay := lay) hR) .nil
  simpa [capWords, valOf, tcap] using h

/-- **K5-3.** For every byte string (bytes < 256), n, OUTMAX < 2³², either reading, every world σ the iteration reaches, and
every loader image (`Layout`, `MemRel`): no word-machine run of the compiled step term reaches the OVERFLOW exit. -/
theorem deflate_noovf {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) {lay : Int → W} {m : WMem}
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∀ j W', WN (lower2T [tcap] stepT []).2 j
      (.run (lower2T [tcap] stepT []).1 (capWords lay p (L0 b.size om)) [], m) W' → W'.1 ≠ .ovf := by
  obtain ⟨f, hw, -, -⟩ := reach_inv (om := om) (lit := lit) hb k _ σ
    ⟨_, initStore_world b om lit p, Inv_init b om lit, Mag_init b om lit⟩ h
  have hsrc : SrcInRange (instL 0 [.const (.cap p)] stepT, σ) := by
    rw [stepT_inst]; exact deflate_inrange hb hn32 hom32 k σ h
  exact compile_noovf [tcap] [true] stepT tcap [.const (.cap p)] _ stepT_typed stepT_wfB stepT_fnOk stepT_ok2 rfl
    (good_cap p) stepT_table (envRel_cap hw.reg) hl hm hsrc

/-- **Row 296 at K5-3.** `compile_refines` (1) at DEFLATE's step term, without its overflow disjunct: a ⟶₂ run of the step
term from a reached world that returns `a` (evaluating to w) is matched by a word-machine run that FINISHES with words related
to w's IR image. -/
theorem deflate_refines_noovf {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) {lay : Int → W} {m : WMem}
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∀ a σ' w, Steps₂ (closeAt p stepT, σ) (.ret a, σ') → Atom.eval a = some w →
      ∃ j ws m', WN (lower2T [tcap] stepT []).2 j
          (.run (lower2T [tcap] stepT []).1 (capWords lay p (L0 b.size om)) [], m) (.done ws, m') ∧
        VRel (lower2T [tcap] stepT []).2 lay σ' tcap (valOf w) ws := by
  obtain ⟨f, hw, -, -⟩ := reach_inv (om := om) (lit := lit) hb k _ σ
    ⟨_, initStore_world b om lit p, Inv_init b om lit, Mag_init b om lit⟩ h
  have hsrc : SrcInRange (instL 0 [.const (.cap p)] stepT, σ) := by
    rw [stepT_inst]; exact deflate_inrange hb hn32 hom32 k σ h
  have := compile_refines_noovf [tcap] [true] stepT tcap [.const (.cap p)] _ stepT_typed stepT_wfB stepT_fnOk stepT_ok2
    rfl (good_cap p) stepT_table (envRel_cap hw.reg) hl hm hsrc
  rw [stepT_inst] at this
  exact this

end K5
