/-
  O95 layer L5, Lean arm (LV8-MAP.md, infrastructure 1): ⟶₅ as a FUNCTION. `stepFn₅` is sound and complete for `Step₅`, and
  `run₅ n` runs at most n steps. DEFLATE's statements run its step term by `run₂` at the constant fuel KSTEP; the re-expressed
  step term runs by `run₅` at the same KSTEP (arm (A)). L2's counterpart is l2's `stepFn₂` (sound) with DEFLATE's
  `stepFn₂_complete`; this file states the same two facts over Tm₅.
-/
import VIRL5.Logic5

namespace VIRL5
open VIRL1 VIRL2

/-- One ⟶₅ step, as a function: `none` exactly when the configuration has no step. -/
def stepFn₅ : Tm₅ → Store → Option Config₅
  | .letE _ (.ret a) e₂, σ => (Atom₅.eval a).map fun v => (e₂.subst 0 v, σ)
  | .letE _ (.retK a []) e₂, σ => (Atom₅.eval a).map fun v => (e₂.subst 0 v, σ)
  | .letE τ e₁ e₂, σ => (stepFn₅ e₁ σ).map fun c => (.letE τ c.1 e₂, c.2)
  | .letOp o as _ e, σ => (Atom₅.evalL as).bind fun vs => (opStep₅ o vs σ).map fun p => (e.subst 0 p.1, p.2)
  | .app a₁ a₂, σ =>
    match Atom₅.eval a₁, Atom₅.eval a₂ with
    | some (.lam _ 0 e), some v => some (e.subst 0 v, σ)
    | some (.fix τ₁ 0 τ₂ e), some v => some ((e.subst 0 v).subst 0 (.fix τ₁ 0 τ₂ e), σ)
    | _, _ => none
  | .ite a e₁ e₂, σ =>
    match Atom₅.eval a with
    | some (.const c) =>
      match Const.toBool c with
      | some true => some (e₁, σ)
      | some false => some (e₂, σ)
      | none => none
    | _ => none
  | .case a e₁ e₂, σ =>
    match Atom₅.eval a with
    | some (.inl _ v) => some (e₁.subst 0 v, σ)
    | some (.inr _ v) => some (e₂.subst 0 v, σ)
    | _ => none
  | .appK a₁ a₂ cs, σ =>
    match Atom₅.eval a₁, Atom₅.eval a₂, Atom₅.evalL cs with
    | some (.lam _ k e), some v, some qs => if qs.length = k then some (Tm₅.substAll (v :: qs) e, σ) else none
    | some (.fix τ₁ k τ₂ e), some v, some qs =>
      if qs.length = k then some (Tm₅.substAll (.fix τ₁ k τ₂ e :: v :: qs) e, σ) else none
    | _, _, _ => none
  | .letK _ j (.retK a ds) e₂, σ =>
    match Atom₅.eval a, Atom₅.evalL ds with
    | some v, some qs => if qs.length = j then some (Tm₅.substAll (v :: qs) e₂, σ) else none
    | _, _ => none
  | .letK _ 0 (.ret a) e₂, σ => (Atom₅.eval a).map fun v => (e₂.subst 0 v, σ)
  | .letK τ j e₁ e₂, σ => (stepFn₅ e₁ σ).map fun c => (.letK τ j c.1 e₂, c.2)
  | _, _ => none

/-- Run at most n steps. -/
def run₅ : Nat → Config₅ → Config₅
  | 0, c => c
  | n + 1, c => match stepFn₅ c.1 c.2 with
    | some c' => run₅ n c'
    | none => c

theorem stepFn₅_ret (a : Atom₅) (σ : Store) : stepFn₅ (.ret a) σ = none := by simp [stepFn₅]
theorem stepFn₅_retK (a : Atom₅) (ds : List Atom₅) (σ : Store) : stepFn₅ (.retK a ds) σ = none := by simp [stepFn₅]

/-- A `letE` whose head is neither `ret` nor `retK _ []` steps under its head. -/
theorem stepFn₅_letE_head {τ : Ty₅} {e₁ e₂ : Tm₅} {σ : Store} (h1 : ∀ a, e₁ ≠ .ret a) (h2 : ∀ a, e₁ ≠ .retK a []) :
    stepFn₅ (.letE τ e₁ e₂) σ = (stepFn₅ e₁ σ).map fun c => (.letE τ c.1 e₂, c.2) := by
  cases e₁ with
  | ret a => exact absurd rfl (h1 a)
  | retK a ds =>
    cases ds with
    | nil => exact absurd rfl (h2 a)
    | cons d ds => simp [stepFn₅]
  | _ => simp only [stepFn₅]

/-- A `letK` whose head is neither `retK` nor (at j = 0) `ret` steps under its head. -/
theorem stepFn₅_letK_head {τ : Ty₅} {j : Nat} {e₁ e₂ : Tm₅} {σ : Store} (h1 : ∀ a ds, e₁ ≠ .retK a ds) (h2 : ∀ a, e₁ ≠ .ret a) :
    stepFn₅ (.letK τ j e₁ e₂) σ = (stepFn₅ e₁ σ).map fun c => (.letK τ j c.1 e₂, c.2) := by
  cases e₁ with
  | ret a => exact absurd rfl (h2 a)
  | retK a ds => exact absurd rfl (h1 a ds)
  | _ => cases j <;> simp only [stepFn₅]

/-- **Complete:** every ⟶₅ step is the function's. -/
theorem stepFn₅_complete {c c' : Config₅} (h : Step₅ c c') : stepFn₅ c.1 c.2 = some c' := by
  induction h with
  | letRet ha => simp [stepFn₅, ha]
  | @letStep τ e₁ e₁' e₂ σ σ' hs ih =>
    have ih' : stepFn₅ e₁ σ = some (e₁', σ') := ih
    cases e₁ with
    | ret a => cases hs
    | retK a ds => cases hs
    | _ => show stepFn₅ (.letE τ _ e₂) σ = _; rw [stepFn₅_letE_head (fun _ h => by cases h) (fun _ h => by cases h), ih']; rfl
  | op h₁ h₂ => simp [stepFn₅, h₁, h₂]
  | appLam h₁ h₂ => simp [stepFn₅, h₁, h₂]
  | appFix h₁ h₂ => simp [stepFn₅, h₁, h₂]
  | iteT h₁ h₂ => simp [stepFn₅, h₁, h₂]
  | iteF h₁ h₂ => simp [stepFn₅, h₁, h₂]
  | caseL h₁ => simp [stepFn₅, h₁]
  | caseR h₁ => simp [stepFn₅, h₁]
  | appKLam h₁ h₂ h₃ h₄ => simp [stepFn₅, h₁, h₂, h₃, h₄]
  | appKFix h₁ h₂ h₃ h₄ => simp [stepFn₅, h₁, h₂, h₃, h₄]
  | letKRet h₁ h₂ h₃ => simp [stepFn₅, h₁, h₂, h₃]
  | letRetK0 h₁ => simp [stepFn₅, h₁]
  | letKRet0 h₁ => simp [stepFn₅, h₁]
  | @letKStep τ j e₁ e₁' e₂ σ σ' hs ih =>
    have ih' : stepFn₅ e₁ σ = some (e₁', σ') := ih
    cases e₁ with
    | ret a => cases hs
    | retK a ds => cases hs
    | _ => show stepFn₅ (.letK τ j _ e₂) σ = _; rw [stepFn₅_letK_head (fun _ _ h => by cases h) (fun _ h => by cases h), ih']; rfl

/-- ⟶₅ is deterministic. -/
theorem step₅_det {c c₁ c₂ : Config₅} (h₁ : Step₅ c c₁) (h₂ : Step₅ c c₂) : c₁ = c₂ := by
  have a := stepFn₅_complete h₁
  have b := stepFn₅_complete h₂
  rw [a] at b
  exact Option.some.inj b

/-- **Sound:** what the function returns is a ⟶₅ step. -/
theorem stepFn₅_sound {e : Tm₅} {σ : Store} {c : Config₅} (h : stepFn₅ e σ = some c) : Step₅ (e, σ) c := by
  fun_induction stepFn₅ e σ generalizing c
  all_goals first
    | (cases h; done)
    | (cases h; first
        | exact .appLam ‹_› ‹_› | exact .appFix ‹_› ‹_› | exact .iteT ‹_› ‹_› | exact .iteF ‹_› ‹_›
        | exact .caseL ‹_› | exact .caseR ‹_› | exact .appKLam ‹_› ‹_› ‹_› rfl | exact .appKFix ‹_› ‹_› ‹_› rfl
        | exact .letKRet ‹_› ‹_› rfl)
    | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
       obtain ⟨vs, hvs, p, hp, rfl⟩ := h
       exact .op hvs hp)
    | (simp only [Option.map_eq_some_iff] at h
       obtain ⟨v, hv, rfl⟩ := h
       first
        | exact .letRet hv | exact .letRetK0 hv | exact .letKRet0 hv
        | exact .letStep (by solve_by_elim) | exact .letKStep (by solve_by_elim))

/-- What `run₅` reaches, ⟶₅* reaches. -/
theorem run₅_steps : ∀ (n : Nat) (c : Config₅), Steps₅ c (run₅ n c)
  | 0, c => .refl c
  | n + 1, c => by
    unfold run₅
    split
    · rename_i c' h; exact .step (stepFn₅_sound h) (run₅_steps n c')
    · exact .refl c

end VIRL5
