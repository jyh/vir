/-
  O95 layer L5, Lean arm (amend-24 LV7 groundwork). The operation rule over ⟶₅, taking L2's OWN operation specifications
  (`OpTriple` on L2's `opStep`: `load_at`, `store_at`, `free_at`, the framed axioms) unchanged, because ⟶₅'s `op` step IS L2's
  `opStep` on the lowered constants. And the deterministic head steps the routines' proofs unroll: `ite`, and a lending call of
  a λ or a fix (the callee's body with the argument and the lent constants substituted; the store untouched).
-/
import VIRL5.Logic5
import VIRL2.Regions

namespace VIRL5
open VIRL1 VIRL2

theorem step₅_letOp_inv {o as τ e σ c'} (h : Step₅ (Tm₅.letOp o as τ e, σ) c') :
    ∃ vs v σ', Atom₅.evalL as = some vs ∧ opStep₅ o vs σ = some (v, σ') ∧ c' = (e.subst 0 v, σ') := by
  cases h with
  | op h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- The `let x:τ ← o(a⃗) in e` rule, from an L2 operation specification on the evaluated constants. -/
theorem letOp_rule₅ {P : Assn} {o : Op} {as : List Atom₅} {τ : Ty₅} {e : Tm₅} {R : Atom₅ → List Atom₅ → Assn}
    {cs : List Const} {Q : Atom₂ → Assn} (hvs : Atom₅.evalL as = some (cs.map Atom₅.const))
    (ho : OpTriple P o (cs.map Atom.const) Q) (hk : ∀ v, Triple₅ (Q v) (e.subst 0 (ιA v)) R) :
    Triple₅ P (.letOp o as τ e) R := by
  intro σ σf hP hd hwf
  obtain ⟨v, σq, hop, hdq, hwfq, hQ⟩ := ho σ σf hP hd hwf
  have hop₅ := op5_of hop
  obtain ⟨hs, hpost, hk'⟩ := hk v σq σf hQ hdq hwfq
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · cases hc with
    | refl => exact fun hf => hf.2 _ (.op hvs hop₅)
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₅_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop₅] at h₂'; cases h₂'
      exact hs c h₂
  · cases hc with
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₅_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop₅] at h₂'; cases h₂'
      exact hpost a σ' h₂
  · cases hc with
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₅_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop₅] at h₂'; cases h₂'
      exact hk' a ds σ' h₂

/-- `if`: the head picks a branch by a boolean constant, deterministically, the store untouched. -/
theorem ite_rule₅ {P : Assn} {a : Atom₅} {e₁ e₂ : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} {b : Bool}
    (ha : a.eval = some (.const (.bool b))) (h : Triple₅ P (if b then e₁ else e₂) Q) : Triple₅ P (.ite a e₁ e₂) Q := by
  refine pure_step_rule₅ (e' := if b then e₁ else e₂) (fun σ => ?_) (fun σ c hc => ?_) h
  · cases b
    · exact .iteF ha rfl
    · exact .iteT ha rfl
  · cases hc with
    | iteT h₁ h₂ => rw [ha] at h₁; cases h₁; cases b <;> simp_all [Const.toBool]
    | iteF h₁ h₂ => rw [ha] at h₁; cases h₁; cases b <;> simp_all [Const.toBool]

/-- A lending call of a fix: it unrolls to the body with the fix, the argument and the lent constants substituted. -/
theorem appKFix_rule₅ {P : Assn} {a₁ a₂ : Atom₅} {cs qs : List Atom₅} {τ₁ τ₂ : Ty₅} {k : Nat} {e : Tm₅} {v : Atom₅}
    {Q : Atom₅ → List Atom₅ → Assn} (h₁ : a₁.eval = some (.fix τ₁ k τ₂ e)) (h₂ : a₂.eval = some v)
    (hqs : Atom₅.evalL cs = some qs) (hl : qs.length = k)
    (h : Triple₅ P (Tm₅.substAll (.fix τ₁ k τ₂ e :: v :: qs) e) Q) : Triple₅ P (.appK a₁ a₂ cs) Q := by
  refine pure_step_rule₅ (fun σ => .appKFix h₁ h₂ hqs hl) (fun σ c hc => ?_) h
  cases hc with
  | appKLam h₁' _ _ _ => rw [h₁] at h₁'; cases h₁'
  | appKFix h₁' h₂' hqs' _ => rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rw [hqs] at hqs'; cases hqs'; rfl

/-- A lending call of a λ. -/
theorem appKLam_rule₅ {P : Assn} {a₁ a₂ : Atom₅} {cs qs : List Atom₅} {τ₁ : Ty₅} {k : Nat} {e : Tm₅} {v : Atom₅}
    {Q : Atom₅ → List Atom₅ → Assn} (h₁ : a₁.eval = some (.lam τ₁ k e)) (h₂ : a₂.eval = some v)
    (hqs : Atom₅.evalL cs = some qs) (hl : qs.length = k)
    (h : Triple₅ P (Tm₅.substAll (v :: qs) e) Q) : Triple₅ P (.appK a₁ a₂ cs) Q := by
  refine pure_step_rule₅ (fun σ => .appKLam h₁ h₂ hqs hl) (fun σ c hc => ?_) h
  cases hc with
  | appKLam h₁' h₂' hqs' _ => rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rw [hqs] at hqs'; cases hqs'; rfl
  | appKFix h₁' _ _ _ => rw [h₁] at h₁'; cases h₁'

end VIRL5
