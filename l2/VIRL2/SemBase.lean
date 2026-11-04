/-
  O95 layer L2, Lean arm. Y5 groundwork (OBJECT-L2 §5 semantic typing, read by erratum L2-E1): facts about ⊢₂'s ATOMS that
  every route to Y5 needs. Atoms never have a capability type; closed well-typed atoms evaluate to values of their type
  (L1's `Atom.eval_total`, re-proved for ⊢₂'s atom rules, which are not L1's).
-/
import VIRL2.Typing2

namespace VIRL2
open VIRL1

mutual
theorem atom_noCap : ∀ {Γ a τ}, HasTypeA₂ Γ a τ → hasCap τ = false
  | _, _, _, .var _ h => h
  | _, _, _, .int => rfl
  | _, _, _, .bool => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .prim (p := p) _ => by cases p <;> rfl
  | _, _, _, .lam h₁ h₂ _ _ _ => by simp [hasCap, h₁, h₂]
  | _, _, _, .fix h₁ h₂ _ _ _ => by simp [hasCap, h₁, h₂]
  | _, _, _, .pair h₁ h₂ => by simp [hasCap, atom_noCap h₁, atom_noCap h₂]
  | _, _, _, .fst h => by have := atom_noCap h; simp [hasCap] at this; exact this.1
  | _, _, _, .snd h => by have := atom_noCap h; simp [hasCap] at this; exact this.2
  | _, _, _, .inl h₂ h => by simp [hasCap, atom_noCap h, h₂]
  | _, _, _, .inr h₁ h => by simp [hasCap, atom_noCap h, h₁]
end

theorem const_typed {Γ : Ctx S₂} {c : Const} (hc : Const.ty c ≠ BTy.cap) : HasTypeA₂ Γ (.const c) (.base (Const.ty c)) := by
  cases c with
  | int => exact .int
  | bool => exact .bool
  | unit => exact .unit
  | cap => exact absurd rfl hc

theorem canon_base₂ {v : Atom₂} {b} (hv : v.IsValue) (h : HasTypeA₂ [] v (.base b)) :
    ∃ c, v = .const c ∧ Const.ty c = b ∧ b ≠ BTy.cap := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  all_goals first | exact ⟨_, rfl, rfl, by decide⟩ | (rename_i h; simp at h)

theorem canon_arr₂ {v : Atom₂} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA₂ [] v (.arr τ₁ τ₂)) :
    (∃ e Δ, v = .lam τ₁ e ∧ Mask.empty Δ ∧ HasType₂ [τ₁] Δ e τ₂) ∨
    (∃ e Δ, v = .fix τ₁ τ₂ e ∧ Mask.empty Δ ∧ HasType₂ [τ₁, .arr τ₁ τ₂] Δ e τ₂) := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  all_goals first | exact .inl ⟨_, _, rfl, ‹_›, ‹_›⟩ | exact .inr ⟨_, _, rfl, ‹_›, ‹_›⟩

theorem canon_prod₂ {v : Atom₂} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA₂ [] v (.prod τ₁ τ₂)) :
    ∃ v₁ v₂, v = .pair v₁ v₂ ∧ v₁.IsValue ∧ v₂.IsValue ∧ HasTypeA₂ [] v₁ τ₁ ∧ HasTypeA₂ [] v₂ τ₂ := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  exact ⟨_, _, rfl, hv.1, hv.2, ‹_›, ‹_›⟩

theorem canon_sum₂ {v : Atom₂} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA₂ [] v (.sum τ₁ τ₂)) :
    (∃ w, v = .inl τ₂ w ∧ w.IsValue ∧ HasTypeA₂ [] w τ₁) ∨ (∃ w, v = .inr τ₁ w ∧ w.IsValue ∧ HasTypeA₂ [] w τ₂) := by
  cases v <;> simp [Atom.IsValue] at hv <;> cases h
  all_goals first | exact .inl ⟨_, rfl, hv, ‹_›⟩ | exact .inr ⟨_, rfl, hv, ‹_›⟩

mutual
theorem eval_total₂ : ∀ (a : Atom₂) {τ}, HasTypeA₂ [] a τ → ∃ v, a.eval = some v ∧ v.IsValue ∧ HasTypeA₂ [] v τ
  | .var _, _, .var h _ => by simp at h
  | .const _, _, .int => ⟨_, rfl, trivial, .int⟩
  | .const _, _, .bool => ⟨_, rfl, trivial, .bool⟩
  | .const _, _, .unit => ⟨_, rfl, trivial, .unit⟩
  | .prim p as, _, .prim h => by
      obtain ⟨cs, hcs, hty⟩ := evalL_total₂ as h
      obtain ⟨c, hc, hct⟩ := lawful.pTotal p cs hty
      have hne : Const.ty c ≠ BTy.cap := by
        have : Const.ty c = BTy.ofL1 (L1.Prim.res p) := hct
        rw [this]; cases L1.Prim.res p <;> decide
      refine ⟨.const c, ?_, trivial, ?_⟩
      · simp only [Atom.eval, hcs, Option.bind_some]
        rw [constsOf_map]; simp only [Option.bind_some]
        rw [show pInterp p cs = some c from hc]; rfl
      · have := const_typed (Γ := []) hne; rw [show Const.ty c = S₂.pRes p from hct] at this; exact this
  | .lam τ e, _, h => ⟨_, rfl, trivial, h⟩
  | .fix τ₁ τ₂ e, _, h => ⟨_, rfl, trivial, h⟩
  | .pair a₁ a₂, _, .pair h₁ h₂ => by
      obtain ⟨v₁, hv₁, hval₁, ht₁⟩ := eval_total₂ a₁ h₁
      obtain ⟨v₂, hv₂, hval₂, ht₂⟩ := eval_total₂ a₂ h₂
      exact ⟨.pair v₁ v₂, by simp [Atom.eval, hv₁, hv₂], ⟨hval₁, hval₂⟩, .pair ht₁ ht₂⟩
  | .fst a, _, .fst h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₂ a h
      obtain ⟨v₁, v₂, rfl, h₁, -, ht₁, -⟩ := canon_prod₂ hval ht
      exact ⟨v₁, by simp [Atom.eval, hv], h₁, ht₁⟩
  | .snd a, _, .snd h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₂ a h
      obtain ⟨v₁, v₂, rfl, -, h₂, -, ht₂⟩ := canon_prod₂ hval ht
      exact ⟨v₂, by simp [Atom.eval, hv], h₂, ht₂⟩
  | .inl τ a, _, .inl hc h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₂ a h
      exact ⟨.inl τ v, by simp [Atom.eval, hv], hval, .inl hc ht⟩
  | .inr τ a, _, .inr hc h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₂ a h
      exact ⟨.inr τ v, by simp [Atom.eval, hv], hval, .inr hc ht⟩
theorem evalL_total₂ : ∀ (as : List Atom₂) {bs : List S₂.B}, HasTypeL₂ [] as (bs.map .base) →
    ∃ cs : List S₂.C, Atom.evalL as = some (cs.map .const) ∧ cs.map S₂.cTy = bs
  | [], [], _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, .cons h hs => by
      obtain ⟨v, hv, hval, hvt⟩ := eval_total₂ a h
      obtain ⟨c, rfl, rfl, -⟩ := canon_base₂ hval hvt
      obtain ⟨cs, hcs, hty⟩ := evalL_total₂ as hs
      exact ⟨c :: cs, by simp [Atom.evalL, hv, hcs], by simp [hty]⟩
end

end VIRL2
