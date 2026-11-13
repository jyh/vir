/-
  O95 compiler, stage S1: the stage theorem `s1_refines` (amend-23 K2: one ∀-program theorem; compiler/DECLARATIONS-S1.md).
  `Match` relates an IR state to an L2 configuration: the IR's frame stack IS ⟶₂'s stack of `let` contexts (`plug`), the
  environment holds the values ⟶₂ substituted, and the store is the same object.
-/
import VIRC.Sim

namespace VIRC
open VIRL1 VIRL2

/-- ⟶₂'s evaluation context: a stack of `let` frames, innermost first. -/
def plug : List (Ty₂ × Tm₂) → Tm₂ → Tm₂
  | [], t => t
  | (τ, e₂) :: fs, t => plug fs (.letE τ t e₂)

def FRel (fr : Frame) (sf : Ty₂ × Tm₂) : Prop :=
  ∃ vs, fr.2 = vs.map valOf ∧ Good vs ∧ TRel 1 vs fr.1 sf.2

inductive Match : St × Store → Config → Prop where
  | mk {c vs k fs t σ} : Good vs → TRel 0 vs c t → List.Forall₂ FRel k fs →
      Match (.run c (vs.map valOf) k, σ) (plug fs t, σ)

/-! ## ⟶₂ inside a context. -/
theorem plug_step : ∀ (fs : List (Ty₂ × Tm₂)) {t t' σ σ'}, Step₂ (t, σ) (t', σ') →
    Step₂ (plug fs t, σ) (plug fs t', σ')
  | [], _, _, _, _, h => h
  | (_, _) :: fs, _, _, _, _, h => plug_step fs (.letStep h)

theorem no_step_ret {a : Atom₂} {σ c'} : ¬ Step₂ (.ret a, σ) c' := by
  intro h; cases h with
  | pure h => cases h

theorem plug_inv : ∀ (fs : List (Ty₂ × Tm₂)) {t σ c'}, Step₂ (plug fs t, σ) c' →
    (∃ t' σ', Step₂ (t, σ) (t', σ') ∧ c' = (plug fs t', σ')) ∨
    (∃ a τ e₂ fs' v, t = .ret a ∧ fs = (τ, e₂) :: fs' ∧ Atom.eval a = some v ∧ c' = (plug fs' (e₂.subst 0 v), σ))
  | [], t, σ, c', h => .inl ⟨c'.1, c'.2, h, rfl⟩
  | (τ, e₂) :: fs, t, σ, c', h => by
      rcases plug_inv fs h with ⟨t'', σ', h', rfl⟩ | ⟨a, _, _, _, _, ht, _⟩
      · cases h' with
        | pure h' =>
          cases h' with
          | letRet hv => exact .inr ⟨_, _, _, _, _, rfl, rfl, hv, rfl⟩
          | letStep h' => exact .inl ⟨_, _, .pure h', rfl⟩
        | letStep h' => exact .inl ⟨_, _, h', rfl⟩
      · cases ht

theorem plug_ret : ∀ (fs : List (Ty₂ × Tm₂)) {t a}, plug fs t = .ret a → fs = [] ∧ t = .ret a
  | [], _, _, h => ⟨rfl, h⟩
  | (_, _) :: fs, _, _, h => by have := (plug_ret fs h).2; cases this

/-! ## Pushing frames: an IR state is driven to one whose code is not a `letE`, with ⟶₂'s term unchanged. -/
def NotLet : Code → Prop
  | .letE _ _ => False
  | _ => True

theorem normalize : ∀ (c : Code) {vs k fs t σ}, Good vs → TRel 0 vs c t → List.Forall₂ FRel k fs →
    ∃ n c' k' fs' t', IRN n (.run c (vs.map valOf) k, σ) (.run c' (vs.map valOf) k', σ) ∧ TRel 0 vs c' t' ∧
      List.Forall₂ FRel k' fs' ∧ plug fs' t' = plug fs t ∧ NotLet c'
  | .letE c₁ c₂, vs, k, fs, _, σ, hg, .letE (τ := τ) (e₂ := e₂) h₁ h₂, hk => by
      obtain ⟨n, c', k', fs', t', hn, h', hk', hp, hl⟩ :=
        normalize c₁ (k := (c₂, vs.map valOf) :: k) (fs := (τ, e₂) :: fs) hg h₁ (.cons ⟨vs, rfl, hg, h₂⟩ hk)
      exact ⟨n + 1, c', k', fs', t', .step rfl hn, h', hk', hp, hl⟩
  | .ret _, _, _, _, _, _, _, h, hk => ⟨0, _, _, _, _, .refl _, h, hk, rfl, trivial⟩
  | .letOp _ _ _, _, _, _, _, _, _, h, hk => ⟨0, _, _, _, _, .refl _, h, hk, rfl, trivial⟩
  | .app _ _, _, _, _, _, _, _, h, hk => ⟨0, _, _, _, _, .refl _, h, hk, rfl, trivial⟩
  | .ite _ _ _, _, _, _, _, _, _, h, hk => ⟨0, _, _, _, _, .refl _, h, hk, rfl, trivial⟩
  | .case _ _ _, _, _, _, _, _, _, h, hk => ⟨0, _, _, _, _, .refl _, h, hk, rfl, trivial⟩

/-! ## Small facts about values. -/
theorem good_inl {τ} {v : Atom₂} (h : Atom.wfB 0 (.inl τ v) = true ∧ Atom.fnOk (.inl τ v) = true ∧
    Atom.eval (.inl τ v) = some (.inl τ v)) : Atom.wfB 0 v = true ∧ Atom.fnOk v = true ∧ Atom.eval v = some v := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Atom.eval, Option.map_eq_some_iff, Atom.inl.injEq] at h3
  obtain ⟨x, hx, -, rfl⟩ := h3
  exact ⟨by simpa [Atom.wfB] using h1, by simpa [Atom.fnOk] using h2, hx⟩

theorem good_inr {τ} {v : Atom₂} (h : Atom.wfB 0 (.inr τ v) = true ∧ Atom.fnOk (.inr τ v) = true ∧
    Atom.eval (.inr τ v) = some (.inr τ v)) : Atom.wfB 0 v = true ∧ Atom.fnOk v = true ∧ Atom.eval v = some v := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Atom.eval, Option.map_eq_some_iff, Atom.inr.injEq] at h3
  obtain ⟨x, hx, -, rfl⟩ := h3
  exact ⟨by simpa [Atom.wfB] using h1, by simpa [Atom.fnOk] using h2, hx⟩

theorem good_const (c : VIRL2.Const) : Atom.wfB 0 (.const c : Atom₂) = true ∧ Atom.fnOk (.const c : Atom₂) = true ∧
    Atom.eval (.const c : Atom₂) = some (.const c) := by simp [Atom.wfB, Atom.fnOk, Atom.eval]

/-! ## ONE ⟶₂ step is matched by ≥ 1 IR step. -/
theorem sim_step {I : St × Store} {S S' : Config} (hm : Match I S) (hs : Step₂ S S') :
    ∃ n I', IRN (n + 1) I I' ∧ Match I' S' := by
  obtain ⟨hg, hr, hk⟩ := hm
  rename_i c vs k fs t σ
  obtain ⟨n₀, c', k', fs', t', hn, hr', hk', hp, hl⟩ := normalize c (σ := σ) hg hr hk
  rw [← hp] at hs
  -- the IR finishes the step from the normalized state in exactly one step
  suffices ∃ I', stepIR (.run c' (vs.map valOf) k', σ) = some I' ∧ Match I' S' by
    obtain ⟨I', h1, h2⟩ := this
    exact ⟨n₀, I', by simpa using IRN.trans hn (.step h1 (.refl _)), h2⟩
  rcases plug_inv fs' hs with ⟨t'', σ', ht, rfl⟩ | ⟨a, τ, e₂, fs'', v, rfl, rfl, hv, rfl⟩
  · cases hr' with
    | ret _ => exact absurd ht no_step_ret
    | letE _ _ => exact absurd hl id
    | letOp hos hck =>
      rename_i op os ck τ as e
      cases ht with
      | pure h => cases h
      | op hvs hop =>
        obtain ⟨cv, rfl⟩ := opStep_res hop
        apply Exists.intro; refine ⟨?_, ?_⟩
        · simp only [stepIR, ARelL.eval hos hg, hvs, Option.map_some, Option.bind_some, opIR_valOf, hop]; rfl
        · exact Match.mk (Good.cons (good_const cv) hg) (TRel.subst hck (.const cv) hg.closed) hk'
    | app h₁ h₂ =>
      rename_i o₁ o₂ a₁ a₂
      cases ht with
      | pure h =>
        cases h with
        | appLam he hv =>
          rename_i τ e w
          have hc₁ := ARel.closed h₁ hg; have hc₂ := ARel.closed h₂ hg
          obtain ⟨hw₁, hf₁, -⟩ := Atom.eval_good a₁ he hc₁.1 hc₁.2
          have gv := Atom.eval_good a₂ hv hc₂.1 hc₂.2
          simp only [Atom.wfB, Atom.fnOk, Bool.and_eq_true] at hw₁ hf₁
          apply Exists.intro; refine ⟨?_, ?_⟩
          · simp only [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg, he, hv, Option.map_some, valOf]; rfl
          · have := Match.mk (k := k') (σ := σ) (vs := [w]) (Good.cons gv (by simp [Good]))
              (TRel.call_lam hf₁.1 hf₁.2 w) hk'
            simpa using this
        | appFix he hv =>
          rename_i τ₁ τ₂ e w
          have hc₁ := ARel.closed h₁ hg; have hc₂ := ARel.closed h₂ hg
          have gf := Atom.eval_good a₁ he hc₁.1 hc₁.2
          have gv := Atom.eval_good a₂ hv hc₂.1 hc₂.2
          have hw₁ := gf.1; have hf₁ := gf.2.1
          simp only [Atom.wfB, Atom.fnOk, Bool.and_eq_true] at hw₁ hf₁
          apply Exists.intro; refine ⟨?_, ?_⟩
          · simp only [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg, he, hv, Option.map_some, valOf]; rfl
          · have := Match.mk (k := k') (σ := σ) (vs := [w, .fix τ₁ τ₂ e]) (Good.cons gv (Good.cons gf (by simp [Good])))
              (TRel.call_fix hw₁ hf₁.2 w gv.1) hk'
            simpa [valOf] using this
    | ite h h₁ h₂ =>
      rename_i o c₁ c₂ a e₁ e₂
      cases ht with
      | pure h' =>
        cases h' with
        | iteT he hb =>
          rename_i cb
          cases cb <;> simp [S₂, Const.toBool] at hb
          subst hb
          exact ⟨_, by simp only [stepIR, ARel.eval h hg, he, Option.map_some, valOf], Match.mk hg h₁ hk'⟩
        | iteF he hb =>
          rename_i cb
          cases cb <;> simp [S₂, Const.toBool] at hb
          subst hb
          exact ⟨_, by simp only [stepIR, ARel.eval h hg, he, Option.map_some, valOf], Match.mk hg h₂ hk'⟩
    | case h h₁ h₂ =>
      rename_i o c₁ c₂ a e₁ e₂
      have hc := ARel.closed h hg
      cases ht with
      | pure h' =>
        cases h' with
        | caseL he =>
          rename_i τ w
          have gw := good_inl (Atom.eval_good a he hc.1 hc.2)
          refine ⟨_, by simp only [stepIR, ARel.eval h hg, he, Option.map_some, valOf]; rfl, ?_⟩
          simpa using Match.mk (k := k') (σ := σ) (Good.cons gw hg) (TRel.subst h₁ w hg.closed) hk'
        | caseR he =>
          rename_i τ w
          have gw := good_inr (Atom.eval_good a he hc.1 hc.2)
          refine ⟨_, by simp only [stepIR, ARel.eval h hg, he, Option.map_some, valOf]; rfl, ?_⟩
          simpa using Match.mk (k := k') (σ := σ) (Good.cons gw hg) (TRel.subst h₂ w hg.closed) hk'
  · -- the context's innermost frame receives a value: the IR pops its frame
    cases hr' with
    | ret h =>
      rename_i o
      obtain ⟨⟨c₂, ρ₂⟩, k'', ⟨vs₂, hρ, hg₂, h₂⟩, hk'', rfl⟩ : ∃ fr k'', FRel fr (τ, e₂) ∧ List.Forall₂ FRel k'' fs'' ∧
          k' = fr :: k'' := by
        cases hk' with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      simp only at hρ; subst hρ
      have hc := ARel.closed h hg
      have gv := Atom.eval_good a hv hc.1 hc.2
      refine ⟨_, by simp only [stepIR, ARel.eval h hg, hv, Option.map_some]; rfl, ?_⟩
      simpa using Match.mk (k := k'') (σ := σ) (Good.cons gv hg₂) (TRel.subst h₂ v hg₂.closed) hk''

/-! ## Runs. -/
/-- n ⟶₂ steps (counted, for the divergence clause). -/
inductive SrcN : Nat → Config → Config → Prop where
  | refl (c) : SrcN 0 c c
  | step {n c c' c''} : Step₂ c c' → SrcN n c' c'' → SrcN (n + 1) c c''

theorem SrcN.of_steps : ∀ {c c'}, Steps₂ c c' → ∃ n, SrcN n c c'
  | _, _, .refl _ => ⟨0, .refl _⟩
  | _, _, .step h hs => let ⟨n, hn⟩ := SrcN.of_steps hs; ⟨n + 1, .step h hn⟩

theorem sim_n : ∀ {n S S'}, SrcN n S S' → ∀ {I}, Match I S → ∃ m I', n ≤ m ∧ IRN m I I' ∧ Match I' S'
  | _, _, _, .refl _, I, hm => ⟨0, I, le_refl _, .refl _, hm⟩
  | _, _, _, .step h hs, _, hm => by
      obtain ⟨n₁, I₁, h₁, hm₁⟩ := sim_step hm h
      obtain ⟨m, I', hle, h₂, hm'⟩ := sim_n hs hm₁
      exact ⟨n₁ + 1 + m, I', by omega, IRN.trans h₁ h₂, hm'⟩

/-! ## A finished ⟶₂ run finishes the IR with the same value and store. -/
theorem match_ret {I S} (hm : Match I S) {a : Atom₂} {w} (hS : S.1 = .ret a) (hw : Atom.eval a = some w) :
    stepIR I = some (.done (valOf w), S.2) := by
  cases hm with
  | mk hg hr hk =>
    obtain ⟨rfl, rfl⟩ := plug_ret _ hS
    cases hk
    cases hr with
    | ret h => simp only [stepIR, ARel.eval h hg, hw, Option.map_some]

/-! ## A faulting ⟶₂ run drives the IR to a stuck `run` state: the fault is observable. -/
theorem match_fault {I S} (hm : Match I S) (hf : Faults S) :
    ∃ n c ρ k σ, IRN n I (.run c ρ k, σ) ∧ stepIR (.run c ρ k, σ) = none := by
  cases hm with
  | mk hg hr hk =>
    rename_i c vs k fs t σ
    obtain ⟨n₀, c', k', fs', t', hn, hr', hk', hp, hl⟩ := normalize c (σ := σ) hg hr hk
    rw [← hp] at hf
    refine ⟨n₀, c', vs.map valOf, k', σ, hn, ?_⟩
    cases h : stepIR (.run c' (vs.map valOf) k', σ) with
    | none => rfl
    | some I₂ =>
      exfalso
      cases hr' with
      | letE _ _ => exact hl
      | ret hra =>
        rename_i o a
        cases hk' with
        | nil => exact hf.1 (by simp [plug, Tm.IsTerminal])
        | cons hfr hrest =>
          rename_i fr sf k'' fs''
          obtain ⟨τ, e₂⟩ := sf
          obtain ⟨c₂, ρ₂⟩ := fr
          simp only [stepIR, ARel.eval hra hg] at h
          cases hv : Atom.eval a with
          | none => simp [hv] at h
          | some v => exact hf.2 _ (plug_step fs'' (.pure (.letRet hv)))
      | letOp hos hck =>
        rename_i op os ck τ as e
        simp only [stepIR, ARelL.eval hos hg] at h
        cases hv : Atom.evalL as with
        | none => simp [hv] at h
        | some ws =>
          simp only [hv, Option.map_some, Option.bind_some, opIR_valOf] at h
          cases ho : opStep op ws σ with
          | none => simp [ho] at h
          | some r => exact hf.2 _ (plug_step fs' (.op hv ho))
      | app h₁ h₂ =>
        rename_i o₁ o₂ a₁ a₂
        simp only [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg] at h
        cases e1 : Atom.eval a₁ with
        | none => simp [e1] at h
        | some w =>
          cases e2 : Atom.eval a₂ with
          | none => cases w <;> simp [e1, e2, valOf] at h
          | some v =>
            cases w <;> simp [e1, e2, valOf] at h
            · exact hf.2 _ (plug_step fs' (.pure (.appLam e1 e2)))
            · exact hf.2 _ (plug_step fs' (.pure (.appFix e1 e2)))
      | ite h₀ h₁ h₂ =>
        rename_i o c₁ c₂ a e₁ e₂
        simp only [stepIR, ARel.eval h₀ hg] at h
        cases e1 : Atom.eval a with
        | none => simp [e1] at h
        | some w =>
          cases w <;> simp [e1, valOf] at h
          rename_i cb
          cases cb <;> try simp at h
          rename_i b
          cases b
          · exact hf.2 _ (plug_step fs' (.pure (.iteF e1 rfl)))
          · exact hf.2 _ (plug_step fs' (.pure (.iteT e1 rfl)))
      | case h₀ h₁ h₂ =>
        rename_i o c₁ c₂ a e₁ e₂
        simp only [stepIR, ARel.eval h₀ hg] at h
        cases e1 : Atom.eval a with
        | none => simp [e1] at h
        | some w =>
          cases w <;> simp [e1, valOf] at h
          · exact hf.2 _ (plug_step fs' (.pure (.caseL e1)))
          · exact hf.2 _ (plug_step fs' (.pure (.caseR e1)))

/-! ## THE STAGE THEOREM. -/
theorem match_init (e : Tm₂) (hok : Fragment.ok e = true) (σ : Store) :
    Match (.run (lowerT e) [] [], σ) (e, σ) := by
  simp only [Fragment.ok, Bool.and_eq_true] at hok
  exact Match.mk (vs := []) (fs := []) (by simp [Good]) (lowerT_rel e hok.1 hok.2) .nil

/-- **S1 (amend-23 K2: one ∀-program theorem).** For EVERY program the compiler ACCEPTS (C2's checked predicate) and every
store: (1) a ⟶₂ run that finishes with `ret a`, where a evaluates to w, is matched by an IR run that finishes with
`valOf w` and the SAME store; (2) a ⟶₂ run that FAULTS is matched by an IR run to a stuck `run` state (the IR's one fault
state); (3) an n-step ⟶₂ run is matched by an IR run of at least n steps, so a divergent program diverges. -/
theorem s1_refines (e : Tm₂) (hok : Fragment.ok e = true) (σ : Store) :
    compileS1 e = some (lowerT e) ∧
    (∀ a σ' w, Steps₂ (e, σ) (.ret a, σ') → Atom.eval a = some w →
      ∃ n, IRN n (.run (lowerT e) [] [], σ) (.done (valOf w), σ')) ∧
    (∀ S, Steps₂ (e, σ) S → Faults S →
      ∃ n c ρ k σ', IRN n (.run (lowerT e) [] [], σ) (.run c ρ k, σ') ∧ stepIR (.run c ρ k, σ') = none) ∧
    (∀ n S, SrcN n (e, σ) S → ∃ m I, n ≤ m ∧ IRN m (.run (lowerT e) [] [], σ) I) := by
  refine ⟨by simp [compileS1, hok], ?_, ?_, ?_⟩
  · intro a σ' w hs hw
    obtain ⟨n, hn⟩ := SrcN.of_steps hs
    obtain ⟨m, I, -, hI, hm⟩ := sim_n hn (match_init e hok σ)
    exact ⟨m + 1, by simpa using IRN.trans hI (.step (match_ret hm rfl hw) (.refl _))⟩
  · intro S hs hf
    obtain ⟨n, hn⟩ := SrcN.of_steps hs
    obtain ⟨m, I, -, hI, hm⟩ := sim_n hn (match_init e hok σ)
    obtain ⟨n', c, ρ, k, σ', h', hst⟩ := match_fault hm hf
    exact ⟨m + n', c, ρ, k, σ', IRN.trans hI h', hst⟩
  · intro n S hn
    obtain ⟨m, I, hle, hI, -⟩ := sim_n hn (match_init e hok σ)
    exact ⟨m, I, hle, hI⟩

/-! ## C2 rejects by evaluation (K2's "rejected, never miscompiled"): a λ that captures a variable is outside the fragment. -/
theorem c2_rejects_open_lam : Fragment.ok (.letE tint (.ret (.const (.int 1)))
    (.ret (.lam tint (.ret (.var 1)))) : Tm₂) = false := by decide

theorem c2_accepts_closed_lam : Fragment.ok (.ret (.lam tint (.ret (.var 0))) : Tm₂) = true := by decide

end VIRC
