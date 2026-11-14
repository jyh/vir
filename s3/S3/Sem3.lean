/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 14): toward StepOk's S2 half. Every word state a word run reaches from
  an SRel-related start is itself SRel-related to some IR state, or is OVF (S2's `sim2_step` and the word machine's determinism).
-/
import S3.Need3
import VIRC.S2

namespace S3
open VIRC X86

theorem wn_terminal {T : Table} : ∀ {j : Nat} {W W₁ : WSt × WMem}, WN T j W W₁ → (W.1 = .ovf ∨ W.1 = .fault) → W₁ = W := by
  intro j W W₁ h hterm
  cases h with
  | refl => rfl
  | step hs _ =>
    obtain ⟨w, m⟩ := W
    rcases hterm with h | h <;> (simp only at h; subst h; simp [stepW] at hs)

/-- **srel_reach.** Along a word run from a state S2 relates to an IR state, every reached word state is related to some IR state,
    or the word machine stopped at OVF or FAULT. -/
theorem srel_reach {T : Table} {lay : Int → W} {τfin : VIRL2.Ty₂} (hT : T.length < 2 ^ 64) :
    ∀ {k : Nat} {W W₁ : WSt × WMem}, WN T k W W₁ → ∀ {I : St × VIRL2.Store}, SRel T lay τfin I W →
      (∃ I₁, SRel T lay τfin I₁ W₁) ∨ (W₁.1 = .ovf ∨ W₁.1 = .fault) := by
  intro k W W₁ h
  induction h with
  | refl W => intro I hI; exact .inl ⟨I, hI⟩
  | step hs hrest ih =>
    intro I hI
    obtain ⟨st, σ⟩ := I
    cases st with
    | done v => cases hI with | done _ => simp [stepW] at hs
    | run c ρ fr =>
      rcases sim2_step hT hI with ⟨_, W₂, hs₂, hterm⟩ | ⟨I', _, W₂, hs₂, hrel⟩
      · rw [hs] at hs₂; cases hs₂
        rw [wn_terminal hrest hterm.symm]; exact .inr hterm.symm
      · rw [hs] at hs₂; cases hs₂
        rcases hrel with hrel | hovf
        · exact ih hrel
        · rw [wn_terminal hrest (.inl hovf)]; exact .inr (.inl hovf)

/-- A capability's words, with its region live under `L.live`, give CapLive. -/
theorem capLive_of {L : Lay3} {ρw : List W} {off : Nat} {σ : VIRL2.Store} {lay : Int → W} {p : Int} {len : Nat}
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) (hR : σ.R.lookup p = some len) (hlen : len < 2 ^ 63)
    (hb : ρw[off]? = some (lay p)) (hn : ρw[off + 1]? = some (BitVec.ofNat 64 len)) : CapLive L ρw off := by
  intro base len' i h1 h2 h3 h4
  rw [hb] at h1; rw [hn] at h2; cases h1; cases h2
  rw [toInt_ofNat_small hlen] at h4
  have hi : i.toInt = i.toNat := by
    have h := BitVec.toInt_eq_toNat_cond i
    split at h
    · exact h
    · rw [h] at h3; have := i.isLt; omega
  apply hlive
  refine ⟨p, len, i.toNat, hR, by omega, ?_⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **stepSem_of_srel.** At a word state S2 relates to an IR state whose live cells `L.live` covers, StepSem holds: the
    capability of a load or store is live (cap_lookup), and a store's index and an app's function are not BAD (opd_sim). -/
theorem stepSem_of_srel {T : Table} {lay : Int → W} {τfin : VIRL2.Ty₂} (hT : T.length < 2 ^ 64) {L : Lay3}
    {I : St × VIRL2.Store} {Wst : WSt × WMem} (h : SRel T lay τfin I Wst) (hlive : ∀ a, VIRBridge.Live I.2 lay a → L.live a) :
    StepSem L Wst.1 := by
  cases h with
  | done _ => trivial
  | run hc hfr hl hm =>
    rename_i c ρ k σ wc ρw kw m τ Γl
    obtain ⟨e, Γt, Δ, t, rfl, rfl, hk, hty, hw, hag, hf, hok, he⟩ := hc
    cases e with
    | ret a => simp [lower2T, StepSem]
    | letE τ₁ e₁ e₂ => simp [lower2T, StepSem]
    | ite a e₁ e₂ => simp [lower2T, StepSem]
    | case a e₁ e₂ => simp only [lower2T]; split <;> simp [StepSem, placeholder]
    | app a₁ a₂ =>
      cases hty with
      | app _ h₁ h₂ =>
        simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
        simp only [Tm.ok2, Bool.and_eq_true] at hok
        simp only [lower2T] at hk ⊢
        obtain ⟨f, _, _, wof⟩ := opd_sim hT t h₁ hw.1 hag he hf.1 hok.1
          (KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) hk)
        simp only [StepSem]
        rcases wof with wof | ⟨_, wof, _⟩ <;> rw [wof] <;> simp
    | letOp o as τ' e' =>
      cases hty with
      | load hg _ ha _ =>
        simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
        simp only [lower2T, lower2L, lower2A, opCode, StepSem]
        have hg' := (hag _ hw.1.1).trans hg
        obtain ⟨p, len, _, hR, hb, hn⟩ := cap_lookup he hg'
        exact capLive_of hlive hR (hl.fits p len hR).2 hb hn
      | store hg _ ha₁ _ _ =>
        simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
        simp only [Tm.fnOk, Atom.fnOkL, Atom.fnOk, Bool.and_eq_true, true_and] at hf
        simp only [Tm.ok2, Atom.ok2L, Atom.ok2, Bool.and_eq_true, true_and] at hok
        simp only [lower2T, lower2L, lower2A, opCode] at hk ⊢
        simp only [StepSem]
        have hg' := (hag _ hw.1.1).trans hg
        obtain ⟨p, len, _, hR, hb, hn⟩ := cap_lookup he hg'
        have k₂ := KeepsFrom.of_keeps (lower2T_keeps _ _ _) hk
        obtain ⟨v₁, _, _, wo₁⟩ := opd_sim hT t ha₁ hw.1.2.1 hag he hf.1.1 hok.1.1
          (KeepsFrom.of_keeps (lower2A_keeps Γl _ _) k₂)
        refine ⟨capLive_of hlive hR (hl.fits p len hR).2 hb hn, ?_⟩
        rcases wo₁ with wo₁ | ⟨_, wo₁, _⟩ <;> rw [wo₁] <;> simp
      | _ => simp [lower2T, lower2L, lower2A, opCode, StepSem, placeholder]

/-! ## S2's steps keep the regions (no alloc or free in an accepted program), so `Live σ lay` is fixed along the run -/

def NoAF : Code → Prop
  | .letOp .alloc _ _ => False
  | .letOp .free _ _ => False
  | _ => True

theorem opStep_R {op : VIRL2.Op} {as : List VIRL2.Atom₂} {σ : VIRL2.Store} {r : VIRL2.Atom₂ × VIRL2.Store}
    (ha : op ≠ .alloc) (hf : op ≠ .free) (h : VIRL2.opStep op as σ = some r) : r.2.R = σ.R := by
  unfold VIRL2.opStep at h
  split at h
  · exact absurd rfl ha
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨x, _, rfl⟩ := h; rfl
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨x, hx, rfl⟩ := h
    unfold VIRL2.Store.store at hx
    split at hx
    · split at hx
      · simp only [Option.some.injEq] at hx; subst hx; rfl
      · simp at hx
    · simp at hx
  · exact absurd rfl hf
  · simp at h

theorem stepIR_R {c : Code} {ρ : List VIRC.Val} {k : List VIRC.Frame} {σ : VIRL2.Store} {I' : St × VIRL2.Store}
    (hc : NoAF c) (h : stepIR (.run c ρ k, σ) = some I') : I'.2.R = σ.R := by
  cases c with
  | letOp op os c' =>
    have ha : op ≠ .alloc := by rintro rfl; exact hc
    have hf : op ≠ .free := by rintro rfl; exact hc
    simp only [stepIR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ws, _, r, hr, rfl⟩ := h
    simp only [opIR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨cs, _, r', hr', rfl⟩ := hr
    exact opStep_R ha hf hr'
  | ret o => cases k <;> simp only [stepIR, Option.map_eq_some_iff] at h <;> (obtain ⟨_, _, rfl⟩ := h; rfl)
  | letE c₁ c₂ => simp only [stepIR, Option.some.injEq] at h; subst h; rfl
  | app f x => simp only [stepIR] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | ite o c₁ c₂ => simp only [stepIR] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | case o c₁ c₂ => simp only [stepIR] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem noAF_of_srel {T : Table} {lay : Int → W} {τfin : VIRL2.Ty₂} {c ρ k σ} {Wst : WSt × WMem}
    (h : SRel T lay τfin (.run c ρ k, σ) Wst) : NoAF c := by
  cases h with
  | run hc _ _ _ =>
    obtain ⟨e, _, _, _, rfl, _, _, _, _, _, _, hok, _⟩ := hc
    cases e with
    | letOp o as τ e' => cases o <;> simp_all [lowerT, NoAF, Tm.ok2]
    | _ => simp [lowerT, NoAF]

/-- **srel_reach_R.** `srel_reach`, with the related IR state's regions those of the start. -/
theorem srel_reach_R {T : Table} {lay : Int → W} {τfin : VIRL2.Ty₂} (hT : T.length < 2 ^ 64) :
    ∀ {k : Nat} {W W₁ : WSt × WMem}, WN T k W W₁ → ∀ {I : St × VIRL2.Store}, SRel T lay τfin I W →
      (∃ I₁, SRel T lay τfin I₁ W₁ ∧ I₁.2.R = I.2.R) ∨ (W₁.1 = .ovf ∨ W₁.1 = .fault) := by
  intro k W W₁ h
  induction h with
  | refl W => intro I hI; exact .inl ⟨I, hI, rfl⟩
  | step hs hrest ih =>
    intro I hI
    obtain ⟨st, σ⟩ := I
    cases st with
    | done v => cases hI with | done _ => simp [stepW] at hs
    | run c ρ fr =>
      rcases sim2_step hT hI with ⟨_, W₂, hs₂, hterm⟩ | ⟨I', hI', W₂, hs₂, hrel⟩
      · rw [hs] at hs₂; cases hs₂
        rw [wn_terminal hrest hterm.symm]; exact .inr hterm.symm
      · rw [hs] at hs₂; cases hs₂
        have hR' := stepIR_R (noAF_of_srel hI) hI'
        rcases hrel with hrel | hovf
        · rcases ih hrel with ⟨I₁, h1, h2⟩ | ht
          · exact .inl ⟨I₁, h1, h2.trans hR'⟩
          · exact .inr ht
        · rw [wn_terminal hrest (.inl hovf)]; exact .inr (.inl hovf)

theorem live_of_R {σ σ' : VIRL2.Store} {lay : Int → W} (hR : σ'.R = σ.R) (a : W) :
    VIRBridge.Live σ' lay a → VIRBridge.Live σ lay a := by
  rintro ⟨p, n, i, h1, h2, h3⟩; exact ⟨p, n, i, by rw [← hR]; exact h1, h2, h3⟩

/-- **s3_refines_from_s2.** S3's run theorem for `lower3`, with StepOk discharged: its BUF half by Fragment3's static clause, and
    its semantic half by S2's relation at the start (`SRel`), with `L.live` covering the start store's live cells. -/
theorem s3_refines_from_s2 {ilen : Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    {lay : Int → W} {τfin : VIRL2.Ty₂} {I₀ : St × VIRL2.Store}
    (hCdef : C = ctxOf ilen tbl main base) (hp : p = lower3 ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    (h0 : SRel tbl lay τfin I₀ (.run main ρ₀ [], wm)) (hlive : ∀ a, VIRBridge.Live I₀.2 lay a → L.live a)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) := by
  refine s3_refines_lower3_static hCdef hp hC hb hT64 hNm hNt hL hcanon hretc hstub hD hrip hrun ?_
  intro k W₁ hk
  rcases srel_reach_R hT64 hk h0 with ⟨I₁, h1, h2⟩ | ht
  · exact stepSem_of_srel hT64 h1 (fun a ha => hlive a (live_of_R h2 a ha))
  · obtain ⟨w, m⟩ := W₁
    rcases ht with ht | ht <;> (simp only at ht; subst ht; trivial)

end S3
