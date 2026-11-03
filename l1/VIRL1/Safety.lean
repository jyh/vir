/-
  O95 layer L1, Lean arm. STEP 5: well-typed programs are safe (OBJECT-L1 §5).
  The hypotheses an L1 theorem carries about Σ (W3b) are exactly `Sig.Lawful` (two fields) and `S.O → False` (O₁ = ∅).
-/
import VIRL1.Typing

namespace VIRL1
variable {S : Sig} {E : ESig S}

/-- What the core needs from a signature: P's interpretation is total at its arity, and a boolean constant reads as one. -/
structure Sig.Lawful (S : Sig) : Prop where
  pTotal : ∀ p cs, cs.map S.cTy = S.pArgs p → ∃ c, S.pInterp p cs = some c ∧ S.cTy c = S.pRes p
  boolCanon : ∀ c, S.cTy c = S.boolTy → ∃ b, S.toBool c = some b

theorem constsOf_map (cs : List S.C) : constsOf (cs.map Atom.const) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [constsOf, ih]

/-! ## Canonical forms -/
theorem canon_base {v : Atom S} {b} (hv : v.IsValue) (h : HasTypeA E [] v (.base b)) : ∃ c, v = .const c ∧ S.cTy c = b := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem canon_arr {v : Atom S} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA E [] v (.arr τ₁ τ₂)) :
    (∃ e, v = .lam τ₁ e ∧ HasType E [τ₁] e τ₂) ∨ (∃ e, v = .fix τ₁ τ₂ e ∧ HasType E [τ₁, .arr τ₁ τ₂] e τ₂) := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  · exact .inl ⟨_, rfl, ‹_›⟩
  · exact .inr ⟨_, rfl, ‹_›⟩

/-! ## Atom evaluation is total on well-typed closed atoms, and typed -/
mutual
theorem Atom.eval_total (hS : S.Lawful) : ∀ (a : Atom S) {τ}, HasTypeA E [] a τ →
    ∃ v, a.eval = some v ∧ v.IsValue ∧ HasTypeA E [] v τ
  | .var _, _, .var h => by simp at h
  | .const c, _, .const => ⟨_, rfl, trivial, .const⟩
  | .prim p as, _, .prim h => by
      obtain ⟨cs, hcs, hty⟩ := Atom.evalL_total hS as h
      obtain ⟨c, hc, hct⟩ := hS.pTotal p cs hty
      refine ⟨.const c, ?_, trivial, hct ▸ .const⟩
      simp [Atom.eval, hcs, constsOf_map, hc]
  | .lam τ e, _, h => ⟨_, rfl, trivial, h⟩
  | .fix τ₁ τ₂ e, _, h => ⟨_, rfl, trivial, h⟩
theorem Atom.evalL_total (hS : S.Lawful) : ∀ (as : List (Atom S)) {bs : List S.B}, HasTypeL E [] as (bs.map .base) →
    ∃ cs : List S.C, Atom.evalL as = some (cs.map .const) ∧ cs.map S.cTy = bs
  | [], [], _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, .cons h hs => by
      obtain ⟨v, hv, hval, hvt⟩ := Atom.eval_total hS a h
      obtain ⟨c, rfl, rfl⟩ := canon_base hval hvt
      obtain ⟨cs, hcs, hty⟩ := Atom.evalL_total hS as hs
      exact ⟨c :: cs, by simp [Atom.evalL, hv, hcs], by simp [hty]⟩
end

theorem Atom.eval_typed (hS : S.Lawful) {a v : Atom S} {τ} (h : HasTypeA E [] a τ) (he : a.eval = some v) :
    v.IsValue ∧ HasTypeA E [] v τ := by
  obtain ⟨v', h', hv, ht⟩ := Atom.eval_total hS a h
  rw [he] at h'; cases h'; exact ⟨hv, ht⟩

/-! ## Preservation -/
theorem preservation (hS : S.Lawful) {e e' : Tm S} (hs : Step e e') : ∀ {τ}, HasType E [] e τ → HasType E [] e' τ := by
  induction hs with
  | letRet ha =>
      intro τ h; cases h with
      | letE h₁ h₂ => cases h₁ with
        | ret ha' => exact HasType.subst0 h₂ (Atom.eval_typed hS ha' ha).2
  | letStep _ ih => intro τ h; cases h with | letE h₁ h₂ => exact .letE (ih h₁) h₂
  | appLam h₁ h₂ =>
      intro τ h; cases h with
      | app ha₁ ha₂ =>
        have hl := (Atom.eval_typed hS ha₁ h₁).2
        cases hl with | lam hb => exact HasType.subst0 hb (Atom.eval_typed hS ha₂ h₂).2
  | appFix h₁ h₂ =>
      intro τ h; cases h with
      | app ha₁ ha₂ =>
        have hl := (Atom.eval_typed hS ha₁ h₁).2
        cases hl with | fix hb =>
          exact HasType.subst0 (HasType.subst0 hb (Atom.eval_typed hS ha₂ h₂).2) (Atom.eval_typed hS ha₁ h₁).2
  | iteT => intro τ h; cases h with | ite _ h₁ _ => exact h₁
  | iteF => intro τ h; cases h with | ite _ _ h₂ => exact h₂

/-! ## Progress (needs O = ∅: L1 has no step rule for an effect operation) -/
theorem progress (hS : S.Lawful) (hO : S.O → False) : ∀ (e : Tm S) {τ}, HasType E [] e τ → e.IsTerminal ∨ ∃ e', Step e e'
  | .ret _, _, _ => .inl trivial
  | .letE _ e₁ _, _, .letE h₁ _ => by
      right
      rcases progress hS hO e₁ h₁ with ht | ⟨e₁', hs⟩
      · cases e₁ with
        | ret a =>
          cases h₁ with | ret ha =>
          obtain ⟨v, hv, -⟩ := Atom.eval_total hS a ha
          exact ⟨_, .letRet hv⟩
        | _ => simp [Tm.IsTerminal] at ht
      · exact ⟨_, .letStep hs⟩
  | .letOp o _ _ _, _, _ => (hO o).elim
  | .app a₁ a₂, _, .app h₁ h₂ => by
      right
      obtain ⟨v₁, hv₁, hval, ht⟩ := Atom.eval_total hS a₁ h₁
      obtain ⟨v₂, hv₂, -⟩ := Atom.eval_total hS a₂ h₂
      rcases canon_arr hval ht with ⟨e, rfl, -⟩ | ⟨e, rfl, -⟩
      · exact ⟨_, .appLam hv₁ hv₂⟩
      · exact ⟨_, .appFix hv₁ hv₂⟩
  | .ite a _ _, _, .ite h _ _ => by
      right
      obtain ⟨v, hv, hval, ht⟩ := Atom.eval_total hS a h
      obtain ⟨c, rfl, hc⟩ := canon_base hval ht
      obtain ⟨b, hb⟩ := hS.boolCanon c hc
      cases b
      · exact ⟨_, .iteF hv hb⟩
      · exact ⟨_, .iteT hv hb⟩

/-! ## Determinism -/
theorem Step.ret_irred {a : Atom S} {e'} : ¬ Step (.ret a) e' := fun h => by cases h

theorem determinism {e e₁ : Tm S} (h₁ : Step e e₁) : ∀ {e₂}, Step e e₂ → e₁ = e₂ := by
  induction h₁ with
  | letRet ha => intro e₂ h; cases h with
    | letRet ha' => rw [ha] at ha'; cases ha'; rfl
    | letStep h' => exact absurd h' Step.ret_irred
  | letStep hs ih => intro e₂ h; cases h with
    | letRet => exact absurd hs Step.ret_irred
    | letStep h' => rw [ih h']
  | appLam h₁ h₂ => intro e₂ h; cases h with
    | appLam h₁' h₂' => rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; rfl
    | appFix h₁' => rw [h₁] at h₁'; cases h₁'
  | appFix h₁ h₂ => intro e₂ h; cases h with
    | appLam h₁' => rw [h₁] at h₁'; cases h₁'
    | appFix h₁' h₂' => rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; rfl
  | iteT ha hb => intro e₂ h; cases h with
    | iteT => rfl
    | iteF ha' hb' => rw [ha] at ha'; cases ha'; rw [hb] at hb'; cases hb'
  | iteF ha hb => intro e₂ h; cases h with
    | iteT ha' hb' => rw [ha] at ha'; cases ha'; rw [hb] at hb'; cases hb'
    | iteF => rfl

/-! ## Safety: no well-typed program gets stuck -/
theorem preservation_steps (hS : S.Lawful) {e e' : Tm S} (hs : Steps e e') {τ} (h : HasType E [] e τ) : HasType E [] e' τ := by
  induction hs with
  | refl => exact h
  | step s _ ih => exact ih (preservation hS s h)

theorem safety (hS : S.Lawful) (hO : S.O → False) {e e' : Tm S} {τ} (h : HasType E [] e τ) (hs : Steps e e') :
    e'.IsTerminal ∨ ∃ e'', Step e' e'' :=
  progress hS hO e' (preservation_steps hS hs h)

end VIRL1
