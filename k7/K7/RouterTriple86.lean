import K7.RouterX86
import VIRL3.RouterTriple
import VIRL2.Triples

/-
  O95, K7 conjunct (2) (compiler/DECLARATIONS-K7.md Addendum 7, the non-author read's test): L3's router triple R4 carried to the x86
  machine through `router_x86` alone. Uses only the instantiation `router_x86`, L3's `R4` (the triple), and generic L2 facts. NO
  `router_inR`, NO `router_halts`, nothing about F's cells or layout. Partial correctness; OVF and RES stay as disjuncts.
-/

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

/-- **router_triple_x86.** R4's premises on the world's contents f, the world `RegionAt 0 87 f σ`, router_x86's premises. For every
finishing source run: the final store is R4's post-state, AND the machine ends DONE with the result related to it, or at OVF, or at
RES (compile_x86's clause 1 at F). -/
theorem router_triple_x86 {σ : Store} {f : Int → Int} (hreg : RegionAt 0 87 f σ)
    (hs0 : 0 ≤ SvA f 0) (hs4 : SvA f 0 < 4) (ht0 : 0 ≤ TvA f 0) (ht4 : TvA f 0 < 4)
    (hw : σ.WF) (hpl : Placed σ) (hc : CellsInR σ)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3}
    (hCdef : C = S3.ctxOf ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base)
    (hP : P = S3.lower3 ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : S3.bytes C (S3.allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hN : 5 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → X86.canonical a = true) (hretc : X86.canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (S3.bytes C (S3.stubHead C)))
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay 0 87) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a)
    {a : Atom₂} {σ' : Store} {w : Atom₂}
    (hs : Steps₂ (instL 0 [(Atom.const (.cap 0) : Atom₂)] F, σ) (.ret a, σ')) (hev : Atom.eval a = some w) :
    RegionAt 0 87 (postF f 0) σ' ∧ ∃ mm,
      (∃ W', S3.R3 C P L W' (X86.runP P mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T [tcap] F []).2 scaleLay σ' tcap (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 (capWords scaleLay 0 87) [], scaleMem σ) Wr ∧
        S3.ResWhy L Wr.1 ∧ S3.ResExit L (X86.runP P mm s)) := by
  have hR : σ.R.lookup 0 = some 87 := by
    have := regionAt_lookup_p (σf := Store.empty) hreg
    rwa [store_empty_union_right] at this
  refine ⟨?_, (router_x86 hR hw hpl hc hCdef hP hC hb hN hL hcanon hretc hstub hD hrip hlive).1 a σ' w hs hev⟩
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  obtain ⟨-, h2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw)
  have hs' : Steps₂ (closeAt 0 F, σ ⊎ Store.empty) (.ret a, σ') := by
    rw [store_empty_union_right]; exact hs
  obtain ⟨v, σq, -, -, hσ', -, -, hq⟩ := h2 _ _ hs'
  rw [hσ', store_empty_union_right]; exact hq

end K7
