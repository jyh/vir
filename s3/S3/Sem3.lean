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

end S3
