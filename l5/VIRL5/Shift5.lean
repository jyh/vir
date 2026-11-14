/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): the de Bruijn SHIFT on ⟶₅ terms. The step's dispatch
  binds the mode at #0 above the world, so each mode's term (world at #0) enters it shifted by one. Two lemmas carry it:
  substituting at the cutoff undoes the shift (`subst_shift₅`), and the shift commutes with substituting a constant one level
  up (`subst_shift_const₅`). With both, a branch reached by the dispatch is the mode's own `t.subst 0 ⟨p⟩`.
-/
import VIRL5.Syntax

namespace VIRL5
open VIRL1 VIRL2

mutual
def Atom₅.shift : Atom₅ → Nat → Atom₅
  | .var n, k => if n < k then .var n else .var (n + 1)
  | .const c, _ => .const c
  | .prim p as, k => .prim p (Atom₅.shiftL k as)
  | .lam τ j e, k => .lam τ j (Tm₅.shift (k + j + 1) e)
  | .fix τ₁ j τ₂ e, k => .fix τ₁ j τ₂ (Tm₅.shift (k + j + 2) e)
  | .pair a₁ a₂, k => .pair (Atom₅.shift a₁ k) (Atom₅.shift a₂ k)
  | .fst a, k => .fst (Atom₅.shift a k)
  | .snd a, k => .snd (Atom₅.shift a k)
  | .inl τ a, k => .inl τ (Atom₅.shift a k)
  | .inr τ a, k => .inr τ (Atom₅.shift a k)
def Atom₅.shiftL (k : Nat) : List Atom₅ → List Atom₅
  | [] => []
  | a :: as => Atom₅.shift a k :: Atom₅.shiftL k as
def Tm₅.shift (k : Nat) : Tm₅ → Tm₅
  | .ret a => .ret (Atom₅.shift a k)
  | .letE τ e₁ e₂ => .letE τ (Tm₅.shift k e₁) (Tm₅.shift (k + 1) e₂)
  | .letOp o as τ e => .letOp o (Atom₅.shiftL k as) τ (Tm₅.shift (k + 1) e)
  | .app a₁ a₂ => .app (Atom₅.shift a₁ k) (Atom₅.shift a₂ k)
  | .ite a e₁ e₂ => .ite (Atom₅.shift a k) (Tm₅.shift k e₁) (Tm₅.shift k e₂)
  | .case a e₁ e₂ => .case (Atom₅.shift a k) (Tm₅.shift (k + 1) e₁) (Tm₅.shift (k + 1) e₂)
  | .retK a ds => .retK (Atom₅.shift a k) (Atom₅.shiftL k ds)
  | .appK a₁ a₂ cs => .appK (Atom₅.shift a₁ k) (Atom₅.shift a₂ k) (Atom₅.shiftL k cs)
  | .letK τ j e₁ e₂ => .letK τ j (Tm₅.shift k e₁) (Tm₅.shift (k + j + 1) e₂)
end

mutual
/-- Substituting at the cutoff undoes the shift. -/
theorem Atom₅.subst_shift : ∀ (a : Atom₅) (k : Nat) (v : Atom₅), (a.shift k).subst k v = a
  | .var n, k, v => by
    by_cases h : n < k
    · simp [Atom₅.shift, Atom₅.subst, h]
    · simp [Atom₅.shift, Atom₅.subst, h, show ¬ n + 1 < k by omega, show n + 1 ≠ k by omega]
  | .const c, k, v => by simp [Atom₅.shift, Atom₅.subst]
  | .prim p as, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.substL_shiftL as k v]
  | .lam τ j e, k, v => by simp [Atom₅.shift, Atom₅.subst, Tm₅.subst_shift e (k + j + 1) v]
  | .fix τ₁ j τ₂ e, k, v => by simp [Atom₅.shift, Atom₅.subst, Tm₅.subst_shift e (k + j + 2) v]
  | .pair a₁ a₂, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift a₁ k v, Atom₅.subst_shift a₂ k v]
  | .fst a, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift a k v]
  | .snd a, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift a k v]
  | .inl τ a, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift a k v]
  | .inr τ a, k, v => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift a k v]
theorem Atom₅.substL_shiftL : ∀ (as : List Atom₅) (k : Nat) (v : Atom₅), Atom₅.substL k v (Atom₅.shiftL k as) = as
  | [], k, v => by simp [Atom₅.shiftL, Atom₅.substL]
  | a :: as, k, v => by simp [Atom₅.shiftL, Atom₅.substL, Atom₅.subst_shift a k v, Atom₅.substL_shiftL as k v]
theorem Tm₅.subst_shift : ∀ (e : Tm₅) (k : Nat) (v : Atom₅), (e.shift k).subst k v = e
  | .ret a, k, v => by simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a k v]
  | .letE τ e₁ e₂, k, v => by simp [Tm₅.shift, Tm₅.subst, Tm₅.subst_shift e₁ k v, Tm₅.subst_shift e₂ (k + 1) v]
  | .letOp o as τ e, k, v => by simp [Tm₅.shift, Tm₅.subst, Atom₅.substL_shiftL as k v, Tm₅.subst_shift e (k + 1) v]
  | .app a₁ a₂, k, v => by simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a₁ k v, Atom₅.subst_shift a₂ k v]
  | .ite a e₁ e₂, k, v => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a k v, Tm₅.subst_shift e₁ k v, Tm₅.subst_shift e₂ k v]
  | .case a e₁ e₂, k, v => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a k v, Tm₅.subst_shift e₁ (k + 1) v, Tm₅.subst_shift e₂ (k + 1) v]
  | .retK a ds, k, v => by simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a k v, Atom₅.substL_shiftL ds k v]
  | .appK a₁ a₂ cs, k, v => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift a₁ k v, Atom₅.subst_shift a₂ k v, Atom₅.substL_shiftL cs k v]
  | .letK τ j e₁ e₂, k, v => by
    simp [Tm₅.shift, Tm₅.subst, Tm₅.subst_shift e₁ k v, Tm₅.subst_shift e₂ (k + j + 1) v]
end

mutual
/-- The shift at k commutes with substituting a constant at k (one level up, k + 1, on the shifted side). -/
theorem Atom₅.subst_shift_const : ∀ (a : Atom₅) (k : Nat) (c : Const),
    (a.shift k).subst (k + 1) (.const c) = (a.subst k (.const c)).shift k
  | .var n, k, c => by
    by_cases h : n < k
    · simp [Atom₅.shift, Atom₅.subst, h, show n < k + 1 by omega]
    · by_cases h' : n = k
      · subst h'; simp [Atom₅.shift, Atom₅.subst]
      · simp [Atom₅.shift, Atom₅.subst, h, h', show ¬ n + 1 < k + 1 by omega, show n + 1 ≠ k + 1 by omega,
          show ¬ n - 1 < k by omega, show n - 1 + 1 = n by omega]
  | .const d, k, c => by simp [Atom₅.shift, Atom₅.subst]
  | .prim p as, k, c => by simp [Atom₅.shift, Atom₅.subst, Atom₅.substL_shiftL_const as k c]
  | .lam τ j e, k, c => by
    have := Tm₅.subst_shift_const e (k + j + 1) c
    simp only [Atom₅.shift, Atom₅.subst, show k + 1 + j + 1 = k + j + 1 + 1 by omega, this]
  | .fix τ₁ j τ₂ e, k, c => by
    have := Tm₅.subst_shift_const e (k + j + 2) c
    simp only [Atom₅.shift, Atom₅.subst, show k + 1 + j + 2 = k + j + 2 + 1 by omega, this]
  | .pair a₁ a₂, k, c => by
    simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift_const a₁ k c, Atom₅.subst_shift_const a₂ k c]
  | .fst a, k, c => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift_const a k c]
  | .snd a, k, c => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift_const a k c]
  | .inl τ a, k, c => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift_const a k c]
  | .inr τ a, k, c => by simp [Atom₅.shift, Atom₅.subst, Atom₅.subst_shift_const a k c]
theorem Atom₅.substL_shiftL_const : ∀ (as : List Atom₅) (k : Nat) (c : Const),
    Atom₅.substL (k + 1) (.const c) (Atom₅.shiftL k as) = Atom₅.shiftL k (Atom₅.substL k (.const c) as)
  | [], k, c => by simp [Atom₅.shiftL, Atom₅.substL]
  | a :: as, k, c => by
    simp [Atom₅.shiftL, Atom₅.substL, Atom₅.subst_shift_const a k c, Atom₅.substL_shiftL_const as k c]
theorem Tm₅.subst_shift_const : ∀ (e : Tm₅) (k : Nat) (c : Const),
    (e.shift k).subst (k + 1) (.const c) = (e.subst k (.const c)).shift k
  | .ret a, k, c => by simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a k c]
  | .letE τ e₁ e₂, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Tm₅.subst_shift_const e₁ k c, Tm₅.subst_shift_const e₂ (k + 1) c]
  | .letOp o as τ e, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.substL_shiftL_const as k c, Tm₅.subst_shift_const e (k + 1) c]
  | .app a₁ a₂, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a₁ k c, Atom₅.subst_shift_const a₂ k c]
  | .ite a e₁ e₂, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a k c, Tm₅.subst_shift_const e₁ k c, Tm₅.subst_shift_const e₂ k c]
  | .case a e₁ e₂, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a k c, Tm₅.subst_shift_const e₁ (k + 1) c,
      Tm₅.subst_shift_const e₂ (k + 1) c]
  | .retK a ds, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a k c, Atom₅.substL_shiftL_const ds k c]
  | .appK a₁ a₂ cs, k, c => by
    simp [Tm₅.shift, Tm₅.subst, Atom₅.subst_shift_const a₁ k c, Atom₅.subst_shift_const a₂ k c,
      Atom₅.substL_shiftL_const cs k c]
  | .letK τ j e₁ e₂, k, c => by
    have := Tm₅.subst_shift_const e₂ (k + j + 1) c
    simp only [Tm₅.shift, Tm₅.subst, Tm₅.subst_shift_const e₁ k c, show k + 1 + j + 1 = k + j + 1 + 1 by omega, this]
end

/-- A branch under the mode binder, at the world ⟨p⟩, reached with the mode value m: the mode's own term at ⟨p⟩. -/
theorem shift_branch₅ (t : Tm₅) (p : Int) (m : Atom₅) :
    ((t.shift 0).subst 1 (.const (.cap p))).subst 0 m = t.subst 0 (.const (.cap p)) := by
  rw [Tm₅.subst_shift_const t 0 (.cap p), Tm₅.subst_shift]

end VIRL5
