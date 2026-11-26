import K7.RouterTriple86
import S3.Proved

/-
  O95 option (iv), OBJECT-NOCHECK NC-R (amend-26 NC6): L3's router triple R4 carried to the x86 machine through the UNCHECKED
  lowering, by `S3.compile_x86_proved`. R4 supplies NC-P′ (`NoFaultP`: its first conjunct, and the `a.eval = some v` of its second).
  No router-specific lemma beyond those `router_triple_x86_p` already uses.
-/

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

/-- **router_triple_x86_proved_p.** `router_triple_x86_p` for `lower3u` (no index checks): the same premises with `ctxOfU`/`lower3u`;
for every finishing source run the final store is R4's post-state, AND the machine ends DONE with the result related to it, or at
OVF, or at RES. -/
theorem router_triple_x86_proved_p {σ : Store} {p : Int} {f : Int → Int} (hreg : RegionAt p 87 f σ)
    (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p) (ht4 : TvA f p < 4)
    (hw : σ.WF) (hpl : Placed σ) (hc : CellsInR σ)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3}
    (hCdef : C = S3.ctxOfU ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base)
    (hP : P = S3.lower3u ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : S3.bytes C (S3.allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hN : 5 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → X86.canonical a = true) (hretc : X86.canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (S3.bytes C (S3.stubHead C)))
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay p 87) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a)
    {a : Atom₂} {σ' : Store} {w : Atom₂}
    (hs : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] F, σ) (.ret a, σ')) (hev : Atom.eval a = some w) :
    RegionAt p 87 (postF f p) σ' ∧ ∃ mm,
      (∃ W', S3.R3 C P L W' (X86.runP P mm s) ∧
        ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T [tcap] F []).2 scaleLay σ' tcap (valOf w) ws) ∨ W'.1 = .ovf)) ∨
      (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 (capWords scaleLay p 87) [], scaleMem σ) Wr ∧
        S3.ResWhy L Wr.1 ∧ S3.ResExit L (X86.runP P mm s)) := by
  have hR : σ.R.lookup p = some 87 := by
    have := regionAt_lookup_p (σf := Store.empty) hreg
    rwa [store_empty_union_right] at this
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  obtain ⟨h1, h2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw)
  have hNF : S3.NoFaultP [(Atom.const (.cap p) : Atom₂)] F σ := by
    refine ⟨fun c hc' => h1 c (by rw [store_empty_union_right]; exact hc'), fun a' σ'' hs'' => ?_⟩
    obtain ⟨v, σq, hv, -⟩ := h2 a' σ'' (by rw [store_empty_union_right]; exact hs'')
    rw [hv]; rfl
  obtain ⟨hl, hm⟩ := loader_ok hw hpl hc
  have hx := S3.compile_x86_proved [tcap] [true] F tcap [.const (.cap p)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap p) F_table
    (envRel_cap1 hR) hl hm hCdef hP hC hb (le_trans F_need hN) (by rw [F_tbl_nil]; intro x hx; cases hx) hL hcanon hretc
    hstub hD hrip hlive hNF
  refine ⟨?_, hx.1 a σ' w hs hev⟩
  have hs' : Steps₂ (closeAt p F, σ ⊎ Store.empty) (.ret a, σ') := by
    rw [store_empty_union_right]; exact hs
  obtain ⟨v, σq, -, -, hσ', -, -, hq⟩ := h2 _ _ hs'
  rw [hσ', store_empty_union_right]; exact hq

end K7
