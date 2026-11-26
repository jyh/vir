import K7.RouterProved
import S3.Entry

/-
  O95, OBJECT-NOCHECK-ENTRY NE-R (amend-27 NE5; errata E1–E3), route file 4: the router's DECIDER dF, of type `tcap` (E3: L2 is
  linear in capabilities, so a decider that reads its capability can only return it). dF reads SvA and TvA by R4's own macro and
  returns its capability when both are in [0, 4); otherwise it loads index −1, an INDEX FAULT, which the CHECKED lowering turns into
  the FAULT status. Its soundness, and the router entered through `S3.compile_entry_run` by an external caller with no proof.

  dF FAULTS by design, so L2's `Triple` (which promises no fault) cannot state its soundness. `PTriple` below is `Triple`'s `ret`
  clause alone: every FINISHING run ends in Q. Its four rules are copies of the ret halves of L2's `letOp_rule` and
  `pure_step_rule`, plus `pload_neg` (a load at a negative index never steps). They are generic and live here because NE4 allows
  new files only.
-/

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

/-! ## Partial triples: the finishing runs only (faults admitted) -/

/-- `Triple`'s `ret` clause alone. -/
def PTriple (P : Assn) (e : Tm₂) (Q : Atom₂ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    ∀ a σ', Steps₂ (e, σ ⊎ σf) (.ret a, σ') →
      ∃ v σq, a.eval = some v ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v σq

theorem ptriple_of {P : Assn} {e : Tm₂} {Q : Atom₂ → Assn} (h : Triple P e Q) : PTriple P e Q :=
  fun σ σf hP hd hwf => (h σ σf hP hd hwf).2

theorem ppre_pure {φ : Prop} {P : Assn} {e : Tm₂} {Q : Atom₂ → Assn} (h : φ → PTriple P e Q) :
    PTriple (fun σ => φ ∧ P σ) e Q := by
  rintro σ σf ⟨hφ, hP⟩ hd hwf; exact h hφ σ σf hP hd hwf

theorem pletOp_rule {P : Assn} {o : Op} {as : List Atom₂} {τ : Ty₂} {e : Tm₂} {R : Atom₂ → Assn} {vs : List Atom₂}
    {Q : Atom₂ → Assn} (hvs : Atom.evalL as = some vs) (ho : OpTriple P o vs Q)
    (hk : ∀ v, PTriple (Q v) (e.subst 0 v) R) : PTriple P (.letOp o as τ e) R := by
  intro σ σf hP hd hwf a σ' hc
  obtain ⟨v, σq, hop, hdq, hwfq, hQ⟩ := ho σ σf hP hd hwf
  cases hc with
  | step h₁ h₂ =>
    obtain ⟨vs', v', σ'', h₁', h₂', rfl⟩ := step₂_letOp_inv h₁
    rw [hvs] at h₁'; cases h₁'; rw [hop] at h₂'; cases h₂'
    exact hk v σq σf hQ hdq hwfq a σ' h₂

theorem ppure_step_rule {P : Assn} {e e' : Tm₂} {Q : Atom₂ → Assn} (hstep : Step e e')
    (hdet : ∀ σ c, Step₂ (e, σ) c → c = (e', σ)) (h : PTriple P e' Q) : PTriple P e Q := by
  intro σ σf hP hd hwf a σ' hc
  cases hc with
  | refl => exact (step_ret_none hstep).elim
  | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact h σ σf hP hd hwf a σ' h₂

/-- A load at a negative index never steps, so no run from it finishes. -/
theorem pload_neg {P : Assn} {p i : Int} {τ : Ty₂} {e : Tm₂} {R : Atom₂ → Assn} (hi : i < 0) :
    PTriple P (.letOp .load [.const (.cap p), .const (.int i)] τ e) R := by
  intro σ σf hP hd hwf a σ' hc
  cases hc with
  | step h₁ _ =>
    obtain ⟨vs', v', σ'', h₁', h₂', -⟩ := step₂_letOp_inv h₁
    simp only [Atom.evalL, Atom.eval, Option.some.injEq] at h₁'
    subst h₁'
    simp only [opStep, Option.map_eq_some_iff] at h₂'
    obtain ⟨x, hx, -⟩ := h₂'
    unfold Store.load at hx
    split at hx
    · rw [if_neg (by omega)] at hx; exact absurd hx (by simp)
    · exact absurd hx (by simp)

theorem pite_true {P : Assn} {a : Atom₂} {e₁ e₂ : Tm₂} {Q : Atom₂ → Assn} {c : Const}
    (ha : Atom.eval a = some (.const c)) (hb : S₂.toBool c = some true) (h : PTriple P e₁ Q) : PTriple P (.ite a e₁ e₂) Q :=
  ppure_step_rule (.iteT ha hb) (det_ite (.iteT ha hb)) h

theorem pite_false {P : Assn} {a : Atom₂} {e₁ e₂ : Tm₂} {Q : Atom₂ → Assn} {c : Const}
    (ha : Atom.eval a = some (.const c)) (hb : S₂.toBool c = some false) (h : PTriple P e₂ Q) : PTriple P (.ite a e₁ e₂) Q :=
  ppure_step_rule (.iteF ha hb) (det_ite (.iteF ha hb)) h

theorem pletRet_rule {P : Assn} {τ : Ty₂} {a v : Atom₂} {e₂ : Tm₂} {Q : Atom₂ → Assn}
    (ha : Atom.eval a = some v) (h : PTriple P (e₂.subst 0 v) Q) : PTriple P (.letE τ (.ret a) e₂) Q :=
  ppure_step_rule (.letRet ha) (det_letRet (.letRet ha)) h

/-- `ld` for partial triples: one load from the world at p, its value substituted. -/
macro "pld" : tactic => `(tactic| (refine pletOp_rule rfl (load_at _ 87 _ _ ?_) (fun v => ppre_pure (fun hv => ?_)); (first | omega | (simp only [A, K, NW, NS, NTp, SvA, TvA, MgA] at *; omega)); subst hv; simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]))
/-- `pl` for partial triples: a pure `let x = ret a`, its value given. -/
macro "ppl" v:term : tactic => `(tactic| (refine pletRet_rule (v := Atom.const (Const.int ($v))) (by simp [Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, MgA, SvA, TvA]) ?_; try simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]))

/-! ## dF -/

/-- The four bounds R4 needs, as one bool atom. -/
def okA : NA := conj (conj (le (.i 0) (.v "s")) (lt (.v "s") (.i 4))) (conj (le (.i 0) (.v "t")) (lt (.v "t") (.i 4)))

/-- dF's body: SvA and TvA by R4's own macro; the capability back if the bounds hold, else a load at index −1 (an index fault). -/
def dFn : NT := RD32 "w" 4 "s" <| RD32 "w" 8 "t" <|
  .ite okA (.ret (.v "w")) (.op "x" tint .load [.v "w", .i (-1)] (.ret (.v "w")))

/-- **dF**, the router's decider, of type `tcap` (E3). -/
def dF : Tm₂ := dFn.c ["w"]

/-- The bool dF tests. -/
def okF (f : Int → Int) (p : Int) : Bool := decide (0 ≤ SvA f p ∧ SvA f p < 4 ∧ 0 ≤ TvA f p ∧ TvA f p < 4)

/-- dF's partial triple: a finishing run returns the capability, the bounds held, and the world is unchanged. -/
theorem dF_ptriple {p : Int} {f : Int → Int} :
    PTriple (RegionAt p 87 f) (closeAt p dF)
      (fun v σ => v = .const (.cap p) ∧ okF f p = true ∧ RegionAt p 87 f σ) := by
  simp only [closeAt, dF, dFn, okA, RD32, NT.c, NA.c, add, mul, le, lt, conj, List.map, List.idxOf, List.findIdx,
    List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  pld; pld; pld; pld; ppl (SvA f p)
  pld; pld; pld; pld; ppl (TvA f p)
  by_cases hok : okF f p = true
  · refine pite_true (c := .bool (okF f p)) ?_ (by rw [hok]; rfl) (ptriple_of (ret_rule' (by simp [Atom.eval]) (fun σ h => ⟨rfl, hok, h⟩)))
    simp [Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, okF, SvA, TvA, Bool.and_assoc]
  · rw [Bool.not_eq_true] at hok
    refine pite_false (c := .bool (okF f p)) ?_ (by rw [hok]; rfl) (pload_neg (by decide))
    simp [Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, okF, SvA, TvA, Bool.and_assoc]

/-- **dF_sound** (NE5's one router lemma). On the router's world, every finishing run of dF leaves the store as it was, returns the
    capability it was given, and gives NC-P′ for F (from R4: a finishing run passed the bounds). -/
theorem dF_sound {σ : Store} {p : Int} {f : Int → Int} (hreg : RegionAt p 87 f σ) (hw : σ.WF) :
    ∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] dF, σ) (.ret a, σ') → Atom.eval a = some w →
      σ' = σ ∧ valOf w = Val.const (.cap p) ∧ S3.NoFaultP [(Atom.const (.cap p) : Atom₂)] F σ := by
  intro a σ' w hs hw'
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  have hs' : Steps₂ (closeAt p dF, σ ⊎ Store.empty) (.ret a, σ') := by rw [store_empty_union_right]; exact hs
  obtain ⟨v, σq, hv, -, hσ', -, hq, hok, hreg'⟩ :=
    dF_ptriple σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw) a σ' hs'
  rw [hw'] at hv; cases hv
  have hσq : σq = σ := by
    obtain ⟨H1, R1⟩ := σq; obtain ⟨H2, R2⟩ := σ
    obtain ⟨hR1, hH1⟩ := hreg'; obtain ⟨hR2, hH2⟩ := hreg
    simp only at hR1 hR2 hH1 hH2
    congr 1
    · exact Finmap.ext_lookup (fun x => by rw [hH1, hH2])
    · rw [hR1, hR2]
  refine ⟨by rw [hσ', store_empty_union_right, hσq], by rw [hq]; simp [valOf], ?_⟩
  simp only [okF, decide_eq_true_eq] at hok
  obtain ⟨hs0, hs4, ht0, ht4⟩ := hok
  obtain ⟨g1, g2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty hreg hdisj (by rw [store_empty_union_right]; exact hw)
  refine ⟨fun c hc' => g1 c (by rw [store_empty_union_right]; exact hc'), fun a' σ'' hs'' => ?_⟩
  obtain ⟨v', σq', hv', -⟩ := g2 a' σ'' (by rw [store_empty_union_right]; exact hs'')
  rw [hv']; rfl

set_option maxHeartbeats 1000000 in
/-- **router_entry (NE-R).** The router F entered by an EXTERNAL caller with no proof, through `S3.compile_entry_run` with the decider
    dF: on the router's world (shape: `RegionAt p₀ 87 f σ`, placed, cells in range), a dF run that faults (dF's reject) or ends in
    OVF/RES reaches XF with memory representing the start; otherwise the machine reaches F's unchecked code in DriverCall and F's
    run is matched as `compile_x86_provedS` states it. No premise on SvA or TvA: dF checks them. -/
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
    (hcodeH : S3.CodeAt Cd P H (.callA based :: S3.loopTail L.env0 XF H₂)) (hcodeH₂ : S3.CodeAt Ce P H₂ [.callA basee])
    (hbased : X86.canonical based = true) (hbasee : X86.canonical basee = true) (hX : X86.canonical XF = true) (hH₂ : X86.canonical H₂ = true)
    (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) (hstk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a)
    {s : X86.Cpu} (hA : S3.AtHead L H [scaleLay p₀, BitVec.ofNat 64 87] m s) :
    (∀ S, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] dF, σ) S → Faults S → S3.AtFaultX P L XF m s) ∧
    (∀ a σ' w, Steps₂ (instL 0 [(Atom.const (.cap p₀) : Atom₂)] dF, σ) (.ret a, σ') → Atom.eval a = some w →
      S3.AtFaultX P L XF m s ∨
      (∃ n₁,
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
  have dF_typed : HasType₂ [tcap] [true] dF tcap := by
    simp only [dF, dFn, okA, RD32, NT.c, NA.c, add, mul, le, lt, conj, List.map, List.idxOf, List.findIdx,
      List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
    l3ty
  exact S3.compile_entry_run dF F tcap dF_typed (by decide) (by decide) (by decide) (by decide) (by decide)
    F_typed F_wfB F_fnOk F_ok2 F_table hR hl hm (dF_sound hreg hw) hCd hsubd hCe hsube hC hbd hbe hNmd hNtd hNme hNte hL hcanon
    hretd hrete hcodeH hcodeH₂ hbased hbasee hX hH₂ hN hE hstk hlive hA

end K7
