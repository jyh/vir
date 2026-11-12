/-
  O95 compiler, K5-1b (compiler/DECLARATIONS-K5.md, addendum 2, written before this file): the in-range premise of K5-1a
  (`InRangeRun`, on the IR run) follows from the SOURCE predicate `SrcInRange` (on the ⟶₂ run), through S1's `Match`.
  Then `compile_noovf`: the compiled program never takes the OVERFLOW exit when the source's int results stay in range.
  S1.lean, Sim2.lean and NoOvf.lean are not edited.
-/
import VIRC.NoOvf
import VIRC.Compose

namespace VIRC
open VIRL1 VIRL2

/-! ## The source predicate. -/
/-- A source atom is in range when it is not an int constant, or an int constant in [−2⁶³, 2⁶³). -/
def Atom.inR₂ : Atom₂ → Prop
  | .const (.int n) => inRange n = true
  | _ => True

mutual
/-- Every primitive sub-atom that evaluates gives an in-range result. -/
def Atom.InR₂ : Atom₂ → Prop
  | .var _ => True
  | .const _ => True
  | .prim p as => Atom.InRL₂ as ∧ ∀ v, Atom.eval (.prim p as) = some v → Atom.inR₂ v
  | .lam _ _ => True
  | .fix _ _ _ => True
  | .pair a₁ a₂ => Atom.InR₂ a₁ ∧ Atom.InR₂ a₂
  | .fst a => Atom.InR₂ a
  | .snd a => Atom.InR₂ a
  | .inl _ a => Atom.InR₂ a
  | .inr _ a => Atom.InR₂ a
def Atom.InRL₂ : List Atom₂ → Prop
  | [] => True
  | a :: as => Atom.InR₂ a ∧ Atom.InRL₂ as
end

/-- The atoms a term's NEXT ⟶₂ step evaluates are in range. -/
def Tm.HeadInR : Tm₂ → Prop
  | .ret a => Atom.InR₂ a
  | .letE _ e₁ _ => Tm.HeadInR e₁
  | .letOp _ as _ _ => Atom.InRL₂ as
  | .app a₁ a₂ => Atom.InR₂ a₁ ∧ Atom.InR₂ a₂
  | .ite a _ _ => Atom.InR₂ a
  | .case a _ _ => Atom.InR₂ a

/-- Every configuration the ⟶₂ run from S₀ reaches evaluates in-range atoms next. A predicate on VALUES, never on bytes. -/
def SrcInRange (S₀ : Config) : Prop := ∀ S, Steps₂ S₀ S → Tm.HeadInR S.1

/-! ## (c) A related operand of an in-range atom is in range. -/
theorem valOf_inR : ∀ {w : Atom₂}, Atom.inR₂ w → (valOf w).inR := by
  intro w h
  cases w with
  | const c => cases c <;> simp_all [Atom.inR₂, valOf, Val.inR]
  | _ => simp [valOf, Val.inR]

mutual
theorem ARel.inR : ∀ {vs o a}, ARel 0 vs o a → Good vs → Atom.InR₂ a → Opd.InR (vs.map valOf) o
  | _, _, _, .varL h, _, _ => by simp [Opd.InR]
  | _, _, _, .varV _ _, _, _ => by simp [Opd.InR]
  | _, _, _, .const, _, _ => by simp [Opd.InR]
  | _, _, _, .lam _ _, _, _ => by simp [Opd.InR]
  | _, _, _, .fix _ _, _, _ => by simp [Opd.InR]
  | _, _, _, .prim (p := p) h, hg, ha => by
      simp only [Atom.InR₂] at ha
      simp only [Opd.InR]; refine ⟨ARelL.inR h hg ha.1, fun v hv => ?_⟩
      rw [ARel.eval (.prim h) hg] at hv
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
      exact valOf_inR (ha.2 w hw)
  | _, _, _, .pair h₁ h₂, hg, ha => by
      simp only [Atom.InR₂] at ha
      simp only [Opd.InR]; exact ⟨ARel.inR h₁ hg ha.1, ARel.inR h₂ hg ha.2⟩
  | _, _, _, .fst h, hg, ha => by simp only [Atom.InR₂] at ha; simp only [Opd.InR]; exact ARel.inR h hg ha
  | _, _, _, .snd h, hg, ha => by simp only [Atom.InR₂] at ha; simp only [Opd.InR]; exact ARel.inR h hg ha
  | _, _, _, .inl h, hg, ha => by simp only [Atom.InR₂] at ha; simp only [Opd.InR]; exact ARel.inR h hg ha
  | _, _, _, .inr h, hg, ha => by simp only [Atom.InR₂] at ha; simp only [Opd.InR]; exact ARel.inR h hg ha
theorem ARelL.inR : ∀ {vs os as}, ARelL 0 vs os as → Good vs → Atom.InRL₂ as → Opd.InRL (vs.map valOf) os
  | _, _, _, .nil, _, _ => by simp [Opd.InRL]
  | _, _, _, .cons h hs, hg, ha => by
      simp only [Atom.InRL₂] at ha
      simp only [Opd.InRL]; exact ⟨ARel.inR h hg ha.1, ARelL.inR hs hg ha.2⟩
end

theorem plug_headInR : ∀ (fs : List (Ty₂ × Tm₂)) (t : Tm₂), Tm.HeadInR (plug fs t) ↔ Tm.HeadInR t
  | [], _ => Iff.rfl
  | (_, _) :: fs, t => by simp only [plug]; rw [plug_headInR fs]; rfl

/-- A matched IR state whose source evaluates in-range atoms next steps on in-range operands. -/
theorem match_stepInR {I S} (hm : Match I S) (hS : Tm.HeadInR S.1) : StepInR I := by
  cases hm with
  | mk hg hr hk =>
    simp only [plug_headInR] at hS
    cases hr with
    | ret h => exact ARel.inR h hg hS
    | letE _ _ => trivial
    | letOp hos _ => exact ARelL.inR hos hg hS
    | app h₁ h₂ => exact ⟨ARel.inR h₁ hg hS.1, ARel.inR h₂ hg hS.2⟩
    | ite h _ _ => exact ARel.inR h hg hS
    | case h _ _ => exact ARel.inR h hg hS

/-! ## (a) One IR step from a matched state. -/
/-- sim_step's case analysis for a NotLet code (a copy of its body after `normalize`, which is the identity there). -/
theorem step_notlet {c' : Code} {vs : List Atom₂} {k' : List Frame} {fs' : List (Ty₂ × Tm₂)} {t' : Tm₂} {σ : Store}
    {S' : Config} (hg : Good vs) (hr' : TRel 0 vs c' t') (hk' : List.Forall₂ FRel k' fs') (hl : NotLet c')
    (hs : Step₂ (plug fs' t', σ) S') :
    ∃ I', stepIR (.run c' (vs.map valOf) k', σ) = some I' ∧ Match I' S' := by
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

theorem src_of_fn {fs : List (Ty₂ × Tm₂)} {t : Tm₂} {σ : Store} (h : stepFn₂ t σ ≠ none) :
    ∃ S', Step₂ (plug fs t, σ) S' := by
  obtain ⟨⟨t', σ'⟩, h⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨_, plug_step fs (stepFn₂_sound h)⟩

/-- An IR step from a matched NotLet state that is not a final `ret` forces a ⟶₂ step of the source. -/
theorem src_steps {c : Code} {vs : List Atom₂} {k : List Frame} {fs : List (Ty₂ × Tm₂)} {t : Tm₂} {σ : Store} {I'}
    (hg : Good vs) (hr : TRel 0 vs c t) (hk : List.Forall₂ FRel k fs) (hl : NotLet c)
    (hs : stepIR (.run c (vs.map valOf) k, σ) = some I') (hnd : ∀ v σ', I' ≠ (.done v, σ')) :
    ∃ S', Step₂ (plug fs t, σ) S' := by
  cases hr with
  | ret h =>
    rename_i o a
    cases hk with
    | nil => cases hv : Atom.eval a <;> simp [stepIR, ARel.eval h hg, hv] at hs; exact absurd hs.symm (hnd _ _)
    | cons hfr hrest =>
      rename_i fr sf k'' fs''
      obtain ⟨τ, e₂⟩ := sf
      obtain ⟨c₂, ρ₂⟩ := fr
      cases hv : Atom.eval a with
      | none => simp [stepIR, ARel.eval h hg, hv] at hs
      | some v => exact ⟨_, plug_step fs'' (.pure (.letRet hv))⟩
  | letE _ _ => exact absurd hl id
  | letOp hos hck =>
    rename_i op os ck τ as e
    cases hvs : Atom.evalL as with
    | none => simp [stepIR, ARelL.eval hos hg, hvs] at hs
    | some ws =>
      cases hop : opStep op ws σ with
      | none => simp [stepIR, ARelL.eval hos hg, hvs, opIR_valOf, hop] at hs
      | some r => exact ⟨_, plug_step fs (.op hvs hop)⟩
  | app h₁ h₂ =>
    rename_i o₁ o₂ a₁ a₂
    apply src_of_fn
    cases e1 : Atom.eval a₁ with
    | none => simp [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg, e1] at hs
    | some w =>
      cases e2 : Atom.eval a₂ with
      | none => cases w <;> simp [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg, e1, e2, valOf] at hs
      | some x =>
        cases w <;> simp [stepIR, ARel.eval h₁ hg, ARel.eval h₂ hg, e1, e2, valOf] at hs
        · simp [stepFn₂, stepFn, e1, e2]
        · simp [stepFn₂, stepFn, e1, e2]
  | ite h h₁ h₂ =>
    rename_i o c₁ c₂ a e₁ e₂
    apply src_of_fn
    cases e1 : Atom.eval a with
    | none => simp [stepIR, ARel.eval h hg, e1] at hs
    | some w =>
      cases w <;> simp [stepIR, ARel.eval h hg, e1, valOf] at hs
      rename_i cb
      cases cb <;> (try simp at hs)
      rename_i b
      cases b
      · simp [stepFn₂, stepFn, e1, S₂, Const.toBool]
      · simp [stepFn₂, stepFn, e1, S₂, Const.toBool]
  | case h h₁ h₂ =>
    rename_i o c₁ c₂ a e₁ e₂
    apply src_of_fn
    cases e1 : Atom.eval a with
    | none => simp [stepIR, ARel.eval h hg, e1] at hs
    | some w =>
      cases w <;> simp [stepIR, ARel.eval h hg, e1, valOf] at hs
      · simp [stepFn₂, stepFn, e1]
      · simp [stepFn₂, stepFn, e1]

theorem ir_step_match {I I' S} (hm : Match I S) (hs : stepIR I = some I') :
    (∃ v σ', I' = (.done v, σ')) ∨ Match I' S ∨ ∃ S', Step₂ S S' ∧ Match I' S' := by
  by_cases hd : ∃ v σ', I' = (.done v, σ')
  · exact .inl hd
  have hnd : ∀ v σ', I' ≠ (.done v, σ') := fun v σ' h => hd ⟨v, σ', h⟩
  cases hm with
  | mk hg hr hk =>
    rename_i c vs k fs t σ
    have notlet : NotLet c → Match I' (plug fs t, σ) ∨ ∃ S', Step₂ (plug fs t, σ) S' ∧ Match I' S' := fun hl => by
      obtain ⟨S', hS'⟩ := src_steps hg hr hk hl hs hnd
      obtain ⟨I'', h1, h2⟩ := step_notlet hg hr hk hl hS'
      rw [hs] at h1; cases h1
      exact .inr ⟨S', hS', h2⟩
    cases c with
    | letE c₁ c₂ =>
      cases hr with
      | letE h₁ h₂ =>
        rename_i τ e₁ e₂
        simp only [stepIR, Option.some.injEq] at hs; subst hs
        exact .inr (.inl (Match.mk (fs := (τ, e₂) :: fs) hg h₁ (.cons ⟨vs, rfl, hg, h₂⟩ hk)))
    | _ => exact .inr (notlet trivial)

/-! ## (b) Every reachable IR state is finished or matched to a reachable source configuration. -/
theorem ir_reach : ∀ {n I₀ I S₀}, Match I₀ S₀ → IRN n I₀ I →
    (∃ v σ', I = (.done v, σ')) ∨ ∃ S, Steps₂ S₀ S ∧ Match I S
  | _, _, _, S₀, hm, .refl _ => .inr ⟨S₀, .refl _, hm⟩
  | _, _, _, S₀, hm, .step hs hrest => by
      rcases ir_step_match hm hs with ⟨v, σ', rfl⟩ | hm' | ⟨S', hS', hm'⟩
      · obtain ⟨-, rfl⟩ := IRN.from_done hrest; exact .inl ⟨v, σ', rfl⟩
      · exact ir_reach hm' hrest
      · rcases ir_reach hm' hrest with hd | ⟨S, hS, hmS⟩
        · exact .inl hd
        · exact .inr ⟨S, .step hS' hS, hmS⟩

/-! ## (d) The transfer, and the compiler-level statement. -/
theorem inRangeRun_of_src {I₀ S₀} (h0 : Match I₀ S₀) (hsrc : SrcInRange S₀) : InRangeRun I₀ := by
  intro n I hI
  rcases ir_reach h0 hI with ⟨v, σ', rfl⟩ | ⟨S, hS, hm⟩
  · trivial
  · exact match_stepInR hm (hsrc S hS)

/-- **K5-1b, `compile_noovf`.** Under `compile_refines`'s hypotheses, if the ⟶₂ run of the instantiated source program
evaluates in-range atoms at every configuration it reaches (`SrcInRange`), then NO word run of the compiled program reaches
the OVERFLOW exit. -/
theorem compile_noovf {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsrc : SrcInRange (instL 0 vs e, σ)) :
    ∀ k W', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W' → W'.1 ≠ .ovf := by
  have hS1 : Match (.run (lowerT e) (vs.map valOf) [], σ) (instL 0 vs e, σ) := by
    have hr := lowerT_rel e (n := 0 + vs.length) (by rw [hlen]; simpa using hw) hf
    have := TRel.inst vs 0 (env := []) hg.closed (by simp [Closed]) hr
    rw [List.append_nil] at this
    exact Match.mk (k := []) (fs := []) (σ := σ) hg this .nil
  exact s2_noovf Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok hT he hl hm (inRangeRun_of_src hS1 hsrc)

/-- `compile_refines` (1) without its overflow disjunct, under `SrcInRange`. -/
theorem compile_refines_noovf {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂)
    (ρw₀ : List W) (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true)
    (hok : Tm.ok2 e = true) (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hsrc : SrcInRange (instL 0 vs e, σ)) :
    ∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w →
      ∃ k ws m', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) (.done ws, m') ∧
        VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws := by
  intro a σ' w hs hw'
  obtain ⟨k, W', hW, r⟩ := (compile_refines Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm).1 a σ' w hs hw'
  rcases r with ⟨ws, m', rfl, hv⟩ | r
  · exact ⟨k, ws, m', hW, hv⟩
  · exact absurd r (compile_noovf Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm hsrc k W' hW)

end VIRC
