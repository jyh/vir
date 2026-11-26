-- PROBE, NOT IN THE LIBRARY (ERRATA-NOCHECK-ENTRY E3): the cap x bool decider; dF_sound builds (ne-r-003); router_entry fails at
-- dF typing, Mask.empty [true] (ne-r-005): a decider that reads its capability can only return the capability (retCap).
import K7.RouterProved
import S3.Entry

/-
  O95, OBJECT-NOCHECK-ENTRY NE-R (amend-27 NE5; errata E1, E2): the router's DECIDER dF, the content half of R4's precondition
  (SvA and TvA in [0, 4)) read as R4 reads it, returned beside the capability as (cap, bool); its soundness; and the router entered
  through `S3.compile_entry_run` by an external caller with no proof.
-/

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

/-- dF's body: SvA and TvA by R4's own macro, then the four bounds as one bool. -/
def dFn : NT := RD32 "w" 4 "s" <| RD32 "w" 8 "t" <|
  .ret (conj (conj (le (.i 0) (.v "s")) (lt (.v "s") (.i 4))) (conj (le (.i 0) (.v "t")) (lt (.v "t") (.i 4))))

/-- **dF**, the router's decider: `let ok = dFn in (w, ok)`. -/
def dF : Tm₂ := .letE tbool (dFn.c ["w"]) (.ret (.pair (.var 1) (.var 0)))

/-- The bool dF computes. -/
def okF (f : Int → Int) (p : Int) : Bool := decide (0 ≤ SvA f p ∧ SvA f p < 4 ∧ 0 ≤ TvA f p ∧ TvA f p < 4)

/-- **dF_sound** (NE5's one router lemma). On the router's world, every finishing run of dF leaves the store as it was, returns the
    capability it was given beside a bool, and a true bool gives NC-P′ for F (from R4). -/
theorem dF_sound {σ : Store} {p : Int} {f : Int → Int} (hreg : RegionAt p 87 f σ) (hw : σ.WF) :
    ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] dF, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ ∃ b, valOf w = Val.pair (Val.const (.cap p)) (Val.const (.bool b)) ∧
        (b = true → S3.NoFaultP [(Atom.const (.cap p) : Atom₂)] F σ) := by
  have htri : Triple (RegionAt p 87 f) (closeAt p dF)
      (fun v σ => v = .pair (.const (.cap p)) (.const (.bool (okF f p))) ∧ RegionAt p 87 f σ) := by
    simp only [closeAt, dF, dFn, RD32, NT.c, NA.c, add, mul, le, lt, conj, List.map, List.idxOf, List.findIdx,
      List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
      Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
    refine letE_rule (Q := fun v σ => v = .const (.bool (okF f p)) ∧ RegionAt p 87 f σ) ?_ (fun v => pre_pure (fun hv => ?_))
    · ld; ld; ld; ld; pl (SvA f p)
      ld; ld; ld; ld; pl (TvA f p)
      refine ret_rule' (by simp [Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, okF, SvA, TvA, Bool.and_assoc])
        (fun σ h => ⟨rfl, h⟩)
    · subst hv
      simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
      exact ret_rule' (by simp [Atom.eval, Atom.evalL]) (fun σ h => ⟨rfl, h⟩)
  intro a σ' w hs hw'
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  obtain ⟨-, h2⟩ := htri σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw)
  have hs' : Steps₂ (closeAt p dF, σ ⊎ Store.empty) (.ret a, σ') := by rw [store_empty_union_right]; exact hs
  obtain ⟨v, σq, hv, -, hσ', -, hq, hreg'⟩ := h2 _ _ hs'
  rw [hw'] at hv; cases hv
  have hσq : σq = σ := by
    obtain ⟨H1, R1⟩ := σq; obtain ⟨H2, R2⟩ := σ
    obtain ⟨hR1, hH1⟩ := hreg'; obtain ⟨hR2, hH2⟩ := hreg
    simp only at hR1 hR2 hH1 hH2
    congr 1
    · exact Finmap.ext_lookup (fun x => by rw [hH1, hH2])
    · rw [hR1, hR2]
  refine ⟨by rw [hσ', store_empty_union_right, hσq], okF f p, by rw [hq]; simp [valOf], fun hb => ?_⟩
  simp only [okF, decide_eq_true_eq] at hb
  obtain ⟨hs0, hs4, ht0, ht4⟩ := hb
  obtain ⟨g1, g2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw)
  refine ⟨fun c hc' => g1 c (by rw [store_empty_union_right]; exact hc'), fun a' σ'' hs'' => ?_⟩
  obtain ⟨v', σq', hv', -⟩ := g2 a' σ'' (by rw [store_empty_union_right]; exact hs'')
  rw [hv']; rfl

set_option maxHeartbeats 1000000 in
/-- **router_entry (NE-R).** The router F entered by an EXTERNAL caller with no proof, through `S3.compile_entry_run` with the decider
    dF: on the router's world (shape: `RegionAt p₀ 87 f σ`, placed, cells in range), a dF run that faults or rejects reaches XF with
    memory representing the start; an accepting run reaches F's unchecked code in DriverCall and F's run is matched as
    `compile_x86_provedS` states it. No premise on SvA or TvA: dF checks them. -/
theorem router_entry {σ : Store} {p₀ : Int} {f : Int → Int} (hreg : RegionAt p₀ 87 f σ) (hw : σ.WF) (hpl : Placed σ)
    (hc : CellsInR σ) {m : VIRC.WMem} (hmdef : m = scaleMem σ)
    {ilen : X86.Op → Nat} {based basee H H₂ XF : VIRC.W} {Cd Ce : S3.Ctx3} {P : X86.Program} {L : S3.Lay3}
    (hCd : Cd = S3.ctxOfB true ilen (lower2T [tcap] dF []).2 (lower2T [tcap] dF []).1 based)
    (hsubd : ∀ a i, (S3.lower3B true ilen (lower2T [tcap] dF []).2 (lower2T [tcap] dF []).1 based).at? a = some i → P.at? a = some i)
    (hCe : Ce = S3.ctxOfU ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 basee)
    (hsube : ∀ a i, (S3.lower3u ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 basee).at? a = some i → P.at? a = some i)
    (hC : ∀ o, 1 ≤ ilen o)
    (hbd : S3.bytes Cd (S3.allCode Cd (lower2T [tcap] dF []).2 (lower2T [tcap] dF []).1) < 2 ^ 64)
    (hbe : S3.bytes Ce (S3.allCode Ce (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hNmd : S3.needW (lower2T [tcap] dF []).1 ≤ L.bufN) (hNtd : ∀ x ∈ (lower2T [tcap] dF []).2, S3.needW x.2 ≤ L.bufN)
    (hNme : S3.needW (lower2T [tcap] F []).1 ≤ L.bufN) (hNte : ∀ x ∈ (lower2T [tcap] F []).2, S3.needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → X86.canonical a = true)
    (hretd : X86.canonical (H + 5) = true) (hrete : X86.canonical (H₂ + 5) = true)
    (hcodeH : S3.CodeAt Cd P H (.callA based :: S3.gateTail L.env0 XF H₂)) (hcodeH₂ : S3.CodeAt Ce P H₂ [.callA basee])
    (hbased : X86.canonical based = true) (hbasee : X86.canonical basee = true) (hX : X86.canonical XF = true) (hH₂ : X86.canonical H₂ = true)
    (hN : 3 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a)
    {s : X86.Cpu} (hA : S3.AtHead L H [scaleLay p₀, BitVec.ofNat 64 87] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] dF, σ) S → Faults S → S3.AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] dF, σ) (.ret a, σ') → Atom.eval a = some w →
      S3.AtFaultX P L XF m s ∨
      (valOf w = Val.pair (Val.const (.cap p₀)) (Val.const (.bool true)) ∧ ∃ n₁,
        (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] F, σ) (.ret a, σ') → Atom.eval a = some w → ∃ mm,
              (∃ W', S3.R3 Ce P (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) W' (X86.runP P mm (X86.runP P n₁ s)) ∧
                ((∃ ws m', W' = (.done ws, m') ∧ VRel (lower2T [tcap] F []).2 scaleLay σ' tcap (valOf w) ws) ∨ W'.1 = .ovf)) ∨
              (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 [scaleLay p₀, BitVec.ofNat 64 87] [], m) Wr ∧ S3.ResWhy (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) Wr.1 ∧
                S3.ResExit (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) (X86.runP P mm (X86.runP P n₁ s)))) ∧
            (∀ n S, SrcN n (instL 0 [(Atom.const (.cap p₀) : Atom₂)] F, σ) S → ∃ mm,
              (∃ W', S3.R3 Ce P (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) W' (X86.runP P mm (X86.runP P n₁ s)) ∧ (n ≤ mm ∨ W'.1 = .ovf)) ∨
              (∃ j Wr, WN (lower2T [tcap] F []).2 j (.run (lower2T [tcap] F []).1 [scaleLay p₀, BitVec.ofNat 64 87] [], m) Wr ∧ S3.ResWhy (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) Wr.1 ∧
                S3.ResExit (S3.Lay3.reRet L (H₂ + 5) (basee + BitVec.ofNat 64 (S3.bytes Ce (S3.stubHead Ce)))) (X86.runP P mm (X86.runP P n₁ s)))))) := by
  subst hmdef
  have hR : σ.R.lookup p₀ = some 87 := by
    have := regionAt_lookup_p (σf := Store.empty) hreg
    rwa [store_empty_union_right] at this
  obtain ⟨hl, hm⟩ := loader_ok hw hpl hc
  have dF_typed : HasType₂ [tcap] [true] dF (.prod tcap tbool) := by
    simp only [dF, dFn, RD32, NT.c, NA.c, add, mul, le, lt, conj, List.map, List.idxOf, List.findIdx,
      List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
    l3ty
  exact S3.compile_entry_run dF F tcap dF_typed (by decide) (by decide) (by decide) (by decide) (by decide)
    F_typed F_wfB F_fnOk F_ok2 F_table hR hl hm (dF_sound hreg hw) hCd hsubd hCe hsube hC hbd hbe hNmd hNtd hNme hNte hL hcanon
    hretd hrete hcodeH hcodeH₂ hbased hbasee hX hH₂ hN hE hstk hlive hA

end K7
