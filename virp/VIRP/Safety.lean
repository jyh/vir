/-
  O95 VIR program, Lean arm. STEP 5: well-typed programs are safe (progress + preservation), and the small-step semantics
  is SOUND against the denotation (a run to a final configuration computes ⟦·⟧). And TERMINATION as a theorem: a well-typed
  program's meaning is DEFINED (`Dom`), with no fuel and no fixpoint (amend-11 V6, V7).
-/
import VIRP.Binders

namespace VIRP

theorem EnvOK.nil : EnvOK [] [] := fun n τ h => by simp at h

theorem EnvOK.cons {Γ : Ctx} {env : List Val} {v : Val} {τ : Ty} (h : EnvOK Γ env) (hv : VTy v τ) :
    EnvOK (some τ :: Γ) (v :: env) := by
  intro n τ' hn
  cases n with
  | zero => simp at hn; subst hn; exact ⟨v, rfl, hv⟩
  | succ m => simpa using h m τ' (by simpa using hn)

/-- Canonical forms: a typed atom evaluates to a value of its type. -/
theorem ATy.eval {Γ : Ctx} {a : Atom} {τ : Ty} (h : ATy Γ a τ) (σ : Store) :
    ∀ {env : List Val}, EnvOK Γ env → ∃ v, a.eval env σ = some v ∧ VTy v τ := by
  induction h with
  | var hn => intro env he; exact he _ _ hn
  | lit => intro _ _; exact ⟨_, rfl, .int⟩
  | bool => intro _ _; exact ⟨_, rfl, .bool⟩
  | sl => intro _ _; exact ⟨_, rfl, .sl⟩
  | tok => intro _ _; exact ⟨_, rfl, .tok⟩
  | magic => intro _ _; exact ⟨_, rfl, .int⟩
  | len _ ih =>
    intro env he; obtain ⟨v, hv, ht⟩ := ih he; cases ht; exact ⟨_, by simp only [Atom.eval, hv]; rfl, .int⟩
  | ge _ _ iha ihb =>
    intro env he; obtain ⟨v, hv, ht⟩ := iha he; obtain ⟨w, hw, hu⟩ := ihb he; cases ht; cases hu
    exact ⟨_, by simp only [Atom.eval, hv, hw]; rfl, .bool⟩
  | eq _ _ iha ihb =>
    intro env he; obtain ⟨v, hv, ht⟩ := iha he; obtain ⟨w, hw, hu⟩ := ihb he; cases ht; cases hu
    exact ⟨_, by simp only [Atom.eval, hv, hw]; rfl, .bool⟩
  | and _ _ iha ihb =>
    intro env he; obtain ⟨v, hv, ht⟩ := iha he; obtain ⟨w, hw, hu⟩ := ihb he; cases ht; cases hu
    exact ⟨_, by simp only [Atom.eval, hv, hw]; rfl, .bool⟩
  | canAccess _ _ iha ihb =>
    intro env he; obtain ⟨v, hv, ht⟩ := iha he; obtain ⟨w, hw, hu⟩ := ihb he; cases ht; cases hu
    exact ⟨_, by simp only [Atom.eval, hv, hw]; rfl, .bool⟩
  | hasTokens _ _ iha ihb =>
    intro env he; obtain ⟨v, hv, ht⟩ := iha he; obtain ⟨w, hw, hu⟩ := ihb he; cases ht; cases hu
    exact ⟨_, by simp only [Atom.eval, hv, hw]; rfl, .bool⟩

theorem Use.aty {Γ Γ' : Ctx} {a : Atom} {τ : Ty} : Use Γ a τ Γ' → ATy Γ a τ
  | .var hn => .var hn
  | .val ha => ha.weaken Γ

theorem Use.envOK {Γ Γ' : Ctx} {a : Atom} {τ : Ty} {env : List Val} (h : Use Γ a τ Γ') (he : EnvOK Γ env) : EnvOK Γ' env := by
  cases h with
  | val _ => exact he
  | var _ =>
    intro m τ' hm
    rw [List.getElem?_set] at hm
    split at hm
    · simp at hm
    · exact he m τ' hm

/-! ## Termination: the meaning of a well-typed program is defined (no fuel, no fixpoint) -/
theorem HasType.den_dom {Γ : Ctx} {e : Tm} (h : HasType Γ e) :
    ∀ {env : List Val}, EnvOK Γ env → ∀ σ, (den e env σ).Dom := by
  induction h with
  | letLinDec hs hp _ ih =>
    intro env he σ
    obtain ⟨v, hv, ht⟩ := hs.aty.eval σ he; cases ht
    obtain ⟨w, hw, hu⟩ := hp.eval σ he; cases hu
    simp only [den, hv, hw]
    exact ih ((hs.envOK he).cons .tok) _
  | advance hb _ ih =>
    intro env he σ
    obtain ⟨v, hv, ht⟩ := hb.aty.eval σ he; cases ht
    simp only [den, hv]
    exact ih ((hb.envOK he).cons .sl) _
  | readU32 hb _ ih =>
    intro env he σ
    obtain ⟨v, hv, ht⟩ := hb.eval σ he; cases ht
    simp only [den, hv]
    exact ih (he.cons .int) _
  | guard hc _ _ ihok iherr =>
    intro env he σ
    obtain ⟨v, hv, ht⟩ := hc.eval σ he; cases ht with
    | bool => rename_i b; cases b <;> simp only [den, hv] <;> [exact iherr he σ; exact ihok he σ]
  | ret hs hb _ =>
    intro env he σ
    obtain ⟨v, hv, ht⟩ := hs.aty.eval σ he; cases ht
    obtain ⟨w, hw, hu⟩ := hb.eval σ (hs.envOK he); cases hu
    simp [den, hv, hw]
  | drop => intro _ _ _; simp [den]

/-! ## Progress and preservation (closed programs) -/
theorem progress {e : Tm} (h : HasType [] e) (σ : Store) :
    (∃ r, Final σ e r) ∨ ∃ σ' e', Step σ e σ' e' := by
  cases h with
  | letLinDec hs hp _ =>
    obtain ⟨v, hv, ht⟩ := hs.aty.eval σ EnvOK.nil; cases ht
    obtain ⟨w, hw, hu⟩ := hp.eval σ EnvOK.nil; cases hu
    exact .inr ⟨_, _, .letLinDec hv hw⟩
  | advance hb _ =>
    obtain ⟨v, hv, ht⟩ := hb.aty.eval σ EnvOK.nil; cases ht
    exact .inr ⟨_, _, .advance hv⟩
  | readU32 hb _ =>
    obtain ⟨v, hv, ht⟩ := hb.eval σ EnvOK.nil; cases ht
    exact .inr ⟨_, _, .readU32 hv⟩
  | guard hc _ _ =>
    obtain ⟨v, hv, ht⟩ := hc.eval σ EnvOK.nil; cases ht with
    | bool => rename_i b; cases b
              · exact .inr ⟨_, _, .guardF hv⟩
              · exact .inr ⟨_, _, .guardT hv⟩
  | ret hs hb _ =>
    obtain ⟨v, hv, ht⟩ := hs.aty.eval σ EnvOK.nil; cases ht
    obtain ⟨w, hw, hu⟩ := hb.eval σ (hs.envOK EnvOK.nil); cases hu
    exact .inl ⟨_, .ret hv hw⟩
  | drop => exact .inl ⟨_, .drop⟩

/-- A closed operand consumes nothing from the empty context. -/
theorem Use.nil {a : Atom} {τ : Ty} {Γ' : Ctx} (h : Use [] a τ Γ') : Γ' = [] := by
  cases h with
  | var hn => simp at hn
  | val _ => rfl

theorem preservation {σ σ' : Store} {e e' : Tm} (hs : Step σ e σ' e') (h : HasType [] e) : HasType [] e' := by
  cases hs with
  | letLinDec _ _ =>
    cases h with
    | letLinDec hu _ he =>
      cases hu.nil
      exact HasType.subst _ (Γ := []) (k := 0) (o := some .tok) he (by simp) (by intro τ' h; cases h; exact .tok)
  | advance _ =>
    cases h with
    | advance hu he =>
      cases hu.nil
      exact HasType.subst _ (Γ := []) (k := 0) (o := some .slice) he (by simp) (by intro τ' h; cases h; exact .sl)
  | readU32 _ =>
    cases h with
    | readU32 _ he =>
      exact HasType.subst _ (Γ := []) (k := 0) (o := some .int) he (by simp) (by intro τ' h; cases h; exact .lit)
  | guardT _ => cases h with | guard _ hok _ => exact hok
  | guardF _ => cases h with | guard _ _ herr => exact herr

/-- SAFETY: a well-typed closed program never gets stuck. -/
theorem safety {σ σ' : Store} {e e' : Tm} (h : HasType [] e) (hs : Steps σ e σ' e') :
    (∃ r, Final σ' e' r) ∨ ∃ σ'' e'', Step σ' e' σ'' e'' := by
  induction hs with
  | refl => exact progress h _
  | step s _ ih => exact ih (preservation s h)

/-! ## Soundness of the small-step semantics against the denotation -/
theorem step_den {σ σ' : Store} {e e' : Tm} (hs : Step σ e σ' e') : den e [] σ = den e' [] σ' := by
  cases hs with
  | letLinDec h1 h2 =>
    simp only [den, h1, h2]
    exact (den_subst (v := .tok) (x := .tok) (fun _ _ => rfl) _ 0 [] _ (by simp)).symm
  | advance h1 =>
    simp only [den, h1]
    exact (den_subst (fun _ _ => rfl) _ 0 [] _ (by simp)).symm
  | readU32 h1 =>
    simp only [den, h1]
    exact (den_subst (fun _ _ => rfl) _ 0 [] _ (by simp)).symm
  | guardT h1 => simp only [den, h1]
  | guardF h1 => simp only [den, h1]

theorem final_den {σ : Store} {e : Tm} {r : Store × Label} (h : Final σ e r) : den e [] σ = Part.some r := by
  cases h with
  | ret h1 h2 => simp [den, h1, h2]
  | drop => rfl

/-- SOUNDNESS: a run of the small-step semantics to a final configuration computes the meaning ⟦e⟧ (drop = abort). -/
theorem soundness {σ σ' : Store} {e e' : Tm} {r : Store × Label} (hs : Steps σ e σ' e') (hf : Final σ' e' r) :
    denote e [] σ = Part.some (abort σ r) := by
  have : den e [] σ = Part.some r := by
    induction hs with
    | refl => exact final_den hf
    | step s _ ih => rw [step_den s]; exact ih hf
  simp [denote, this]

end VIRP
