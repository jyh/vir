/-
  O95 layer L5, Lean arm (amend-24 LV4 groundwork). L2's SemBase restated for ⊢₅ (part of `L5.syntaxCopy`): atoms never have a
  capability type; closed well-typed atoms evaluate to values of their type; canonical forms, with the arrow carrying k. Plus the
  one new fact: a CLOSED runtime capability list is all constants ⟨p⟩, exactly the owned Ω (`CapsRT.closed`).
-/
import VIRL5.RTSubst5
import VIRL2.SemBase

namespace VIRL5
open VIRL1 VIRL2

mutual
theorem atom_noCap₅ : ∀ {Γ a τ}, HasTypeA₅ Γ a τ → τ.hasCap = false
  | _, _, _, .var _ h => h
  | _, _, _, .int => rfl
  | _, _, _, .bool => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .prim (p := p) _ => by cases p <;> rfl
  | _, _, _, .lam h₁ h₂ _ _ _ => by simp [Ty₅.hasCap, h₁, h₂]
  | _, _, _, .fix h₁ h₂ _ _ _ => by simp [Ty₅.hasCap, h₁, h₂]
  | _, _, _, .pair h₁ h₂ => by simp [Ty₅.hasCap, atom_noCap₅ h₁, atom_noCap₅ h₂]
  | _, _, _, .fst h => by have := atom_noCap₅ h; simp [Ty₅.hasCap] at this; exact this.1
  | _, _, _, .snd h => by have := atom_noCap₅ h; simp [Ty₅.hasCap] at this; exact this.2
  | _, _, _, .inl h₂ h => by simp [Ty₅.hasCap, atom_noCap₅ h, h₂]
  | _, _, _, .inr h₁ h => by simp [Ty₅.hasCap, atom_noCap₅ h, h₁]
end

theorem const_typed₅ {Γ : Ctx₅} {c : Const} (hc : Const.ty c ≠ BTy.cap) : HasTypeA₅ Γ (.const c) (.base (Const.ty c)) := by
  cases c with
  | int => exact .int
  | bool => exact .bool
  | unit => exact .unit
  | cap => exact absurd rfl hc

theorem canon_base₅ {v : Atom₅} {b} (hv : v.IsValue) (h : HasTypeA₅ [] v (.base b)) :
    ∃ c, v = .const c ∧ Const.ty c = b ∧ b ≠ BTy.cap := by
  cases v <;> simp [Atom₅.IsValue] at hv <;> cases h
  all_goals first | exact ⟨_, rfl, rfl, by decide⟩ | (rename_i h; simp at h)

theorem canon_int₅ {v : Atom₅} (hv : v.IsValue) (h : HasTypeA₅ [] v t5int) : ∃ k, v = .const (.int k) := by
  obtain ⟨c, rfl, hc, -⟩ := canon_base₅ hv h; cases c <;> simp_all [Const.ty]

theorem canon_bool₅ {v : Atom₅} (hv : v.IsValue) (h : HasTypeA₅ [] v t5bool) : ∃ b, v = .const (.bool b) := by
  obtain ⟨c, rfl, hc, -⟩ := canon_base₅ hv h; cases c <;> simp_all [Const.ty]

theorem canon_prod₅ {v : Atom₅} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA₅ [] v (.prod τ₁ τ₂)) :
    ∃ v₁ v₂, v = .pair v₁ v₂ ∧ v₁.IsValue ∧ v₂.IsValue ∧ HasTypeA₅ [] v₁ τ₁ ∧ HasTypeA₅ [] v₂ τ₂ := by
  cases v <;> simp [Atom₅.IsValue] at hv <;> cases h
  exact ⟨_, _, rfl, hv.1, hv.2, ‹_›, ‹_›⟩

theorem canon_sum₅ {v : Atom₅} {τ₁ τ₂} (hv : v.IsValue) (h : HasTypeA₅ [] v (.sum τ₁ τ₂)) :
    (∃ w, v = .inl τ₂ w ∧ w.IsValue ∧ HasTypeA₅ [] w τ₁) ∨ (∃ w, v = .inr τ₁ w ∧ w.IsValue ∧ HasTypeA₅ [] w τ₂) := by
  cases v <;> simp [Atom₅.IsValue] at hv <;> cases h
  all_goals first | exact .inl ⟨_, rfl, hv, ‹_›⟩ | exact .inr ⟨_, rfl, hv, ‹_›⟩

theorem constsOf₅_map : ∀ cs : List Const, constsOf₅ (cs.map Atom₅.const) = some cs
  | [] => rfl
  | c :: cs => by simp [constsOf₅, constsOf₅_map cs]

mutual
theorem eval_total₅ : ∀ (a : Atom₅) {τ}, HasTypeA₅ [] a τ → ∃ v, a.eval = some v ∧ v.IsValue ∧ HasTypeA₅ [] v τ
  | .var _, _, .var h _ => by simp at h
  | .const _, _, .int => ⟨_, rfl, trivial, .int⟩
  | .const _, _, .bool => ⟨_, rfl, trivial, .bool⟩
  | .const _, _, .unit => ⟨_, rfl, trivial, .unit⟩
  | .prim p as, _, .prim h => by
      obtain ⟨cs, hcs, hty⟩ := evalL_total₅ as h
      obtain ⟨c, hc, hct⟩ := lawful.pTotal p cs hty
      have hne : Const.ty c ≠ BTy.cap := by
        have : Const.ty c = BTy.ofL1 (L1.Prim.res p) := hct
        rw [this]; cases L1.Prim.res p <;> decide
      refine ⟨.const c, ?_, trivial, ?_⟩
      · simp only [Atom₅.eval, hcs, Option.bind_some]
        rw [constsOf₅_map]; simp only [Option.bind_some]
        rw [show pInterp p cs = some c from hc]; rfl
      · have := const_typed₅ (Γ := []) hne; rw [show Const.ty c = BTy.ofL1 (L1.Prim.res p) from hct] at this; exact this
  | .lam τ k e, _, h => ⟨_, rfl, trivial, h⟩
  | .fix τ₁ k τ₂ e, _, h => ⟨_, rfl, trivial, h⟩
  | .pair a₁ a₂, _, .pair h₁ h₂ => by
      obtain ⟨v₁, hv₁, hval₁, ht₁⟩ := eval_total₅ a₁ h₁
      obtain ⟨v₂, hv₂, hval₂, ht₂⟩ := eval_total₅ a₂ h₂
      exact ⟨.pair v₁ v₂, by simp [Atom₅.eval, hv₁, hv₂], ⟨hval₁, hval₂⟩, .pair ht₁ ht₂⟩
  | .fst a, _, .fst h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₅ a h
      obtain ⟨v₁, v₂, rfl, h₁, -, ht₁, -⟩ := canon_prod₅ hval ht
      exact ⟨v₁, by simp [Atom₅.eval, hv], h₁, ht₁⟩
  | .snd a, _, .snd h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₅ a h
      obtain ⟨v₁, v₂, rfl, -, h₂, -, ht₂⟩ := canon_prod₅ hval ht
      exact ⟨v₂, by simp [Atom₅.eval, hv], h₂, ht₂⟩
  | .inl τ a, _, .inl hc h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₅ a h
      exact ⟨.inl τ v, by simp [Atom₅.eval, hv], hval, .inl hc ht⟩
  | .inr τ a, _, .inr hc h => by
      obtain ⟨v, hv, hval, ht⟩ := eval_total₅ a h
      exact ⟨.inr τ v, by simp [Atom₅.eval, hv], hval, .inr hc ht⟩
theorem evalL_total₅ : ∀ (as : List Atom₅) {bs : List L1.BTy},
    HasTypeL₅ [] as (bs.map fun b => .base (BTy.ofL1 b)) →
    ∃ cs : List Const, Atom₅.evalL as = some (cs.map .const) ∧ cs.map Const.ty = bs.map BTy.ofL1
  | [], [], _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, .cons h hs => by
      obtain ⟨v, hv, hval, hvt⟩ := eval_total₅ a h
      obtain ⟨c, rfl, hc, -⟩ := canon_base₅ hval hvt
      obtain ⟨cs, hcs, hty⟩ := evalL_total₅ as hs
      exact ⟨c :: cs, by simp [Atom₅.evalL, hv, hcs], by simp [hty, hc]⟩
end

/-- The capability constants ⟨p⟩ of a list of pointers. -/
def capConsts (ps : List Int) : List Atom₅ := ps.map fun p => .const (.cap p)

theorem capConsts_length (ps : List Int) : (capConsts ps).length = ps.length := by simp [capConsts]

theorem evalL_capConsts : ∀ ps : List Int, Atom₅.evalL (capConsts ps) = some (capConsts ps)
  | [] => rfl
  | p :: ps => by simp [capConsts, Atom₅.evalL, Atom₅.eval] at *; exact evalL_capConsts ps

/-- A CLOSED runtime capability list is all constants, and they are exactly what is owned (up to order). -/
theorem CapsRT.closed : ∀ {Δ : List Bool} {Ω : List Int} {ds : List Atom₅}, CapsRT [] Δ Ω ds →
    ∃ ps, ds = capConsts ps ∧ Ω.Perm ps
  | _, Ω, [], h => ⟨[], rfl, by simpa [capPtrs] using h.2.2⟩
  | Δ, Ω, d :: ds, ⟨hf, hx, hp⟩ => by
      rcases hf d (by simp) with ⟨n, rfl⟩ | ⟨p, rfl⟩
      · have := hx.2.1 n (by simp [capVars]); simp at this
      · have hrest : CapsRT [] Δ (capPtrs ds) ds :=
          ⟨fun d hd => hf d (by simp [hd]), by simpa [capVars] using hx, .refl _⟩
        obtain ⟨ps, rfl, hps⟩ := CapsRT.closed hrest
        exact ⟨p :: ps, rfl, hp.trans (by simpa [capPtrs] using hps.cons p)⟩

end VIRL5
