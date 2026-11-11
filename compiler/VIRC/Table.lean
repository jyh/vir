/-
  O95 compiler, stage S2: the code table only GROWS, and an entry below the incoming length is never changed. A label handed
  out for a λ/fix atom therefore names the same entry in the final table as at the moment it was assigned. This is the fact the
  code-value relation rests on.
-/
import VIRC.Layout

namespace VIRC
open VIRL1 VIRL2

/-- `t'` keeps `t`: at least as long, and equal at every index of `t`. -/
def Keeps (t t' : Table) : Prop := t.length ≤ t'.length ∧ ∀ i, i < t.length → t'[i]? = t[i]?

theorem Keeps.refl (t : Table) : Keeps t t := ⟨le_refl _, fun _ _ => rfl⟩

theorem Keeps.trans {a b c : Table} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  ⟨le_trans h₁.1 h₂.1, fun i hi => by rw [h₂.2 i (lt_of_lt_of_le hi h₁.1), h₁.2 i hi]⟩

/-- Reserve a slot, lower a body into the extended table, then fill the slot: the original table is kept. -/
theorem Keeps.reserve (t : Table) (x y : Bool × WCode) (t' : Table) (h : Keeps (t ++ [x]) t') :
    Keeps t (t'.set t.length y) := by
  refine ⟨by simp; have := h.1; simp at this; omega, fun i hi => ?_⟩
  rw [List.getElem?_set_ne (by omega), h.2 i (by simp; omega), List.getElem?_append_left hi]

mutual
theorem lower2A_keeps : ∀ (Γ : Ctx S₂) (a : Atom₂) (t : Table), Keeps t (lower2A Γ a t).2
  | _, .var _, t => Keeps.refl t
  | _, .const (.int _), t => Keeps.refl t
  | _, .const (.bool _), t => Keeps.refl t
  | _, .const .unit, t => Keeps.refl t
  | _, .const (.cap _), t => Keeps.refl t
  | Γ, .prim _ as, t => by simp only [lower2A]; exact lower2L_keeps Γ as t
  | _, .lam τ e, t => by simp only [lower2A]; exact Keeps.reserve t _ _ _ (lower2T_keeps _ e _)
  | _, .fix τ₁ τ₂ e, t => by simp only [lower2A]; exact Keeps.reserve t _ _ _ (lower2T_keeps _ e _)
  | Γ, .pair a₁ a₂, t => by
      simp only [lower2A]; exact Keeps.trans (lower2A_keeps Γ a₁ t) (lower2A_keeps Γ a₂ _)
  | Γ, .fst a, t => by simp only [lower2A]; split <;> exact lower2A_keeps Γ a t
  | Γ, .snd a, t => by simp only [lower2A]; split <;> exact lower2A_keeps Γ a t
  | Γ, .inl _ a, t => by simp only [lower2A]; split <;> exact lower2A_keeps Γ a t
  | Γ, .inr _ a, t => by simp only [lower2A]; split <;> exact lower2A_keeps Γ a t
theorem lower2L_keeps : ∀ (Γ : Ctx S₂) (as : List Atom₂) (t : Table), Keeps t (lower2L Γ as t).2
  | _, [], t => Keeps.refl t
  | Γ, a :: as, t => by
      simp only [lower2L]; exact Keeps.trans (lower2A_keeps Γ a t) (lower2L_keeps Γ as _)
theorem lower2T_keeps : ∀ (Γ : Ctx S₂) (e : Tm₂) (t : Table), Keeps t (lower2T Γ e t).2
  | Γ, .ret a, t => by simp only [lower2T]; exact lower2A_keeps Γ a t
  | Γ, .letE τ e₁ e₂, t => by
      simp only [lower2T]; exact Keeps.trans (lower2T_keeps Γ e₁ t) (lower2T_keeps _ e₂ _)
  | Γ, .letOp _ as τ e, t => by
      simp only [lower2T]; exact Keeps.trans (lower2L_keeps Γ as t) (lower2T_keeps _ e _)
  | Γ, .app a₁ a₂, t => by
      simp only [lower2T]; exact Keeps.trans (lower2A_keeps Γ a₁ t) (lower2A_keeps Γ a₂ _)
  | Γ, .ite a e₁ e₂, t => by
      simp only [lower2T]
      exact Keeps.trans (lower2A_keeps Γ a t) (Keeps.trans (lower2T_keeps Γ e₁ _) (lower2T_keeps Γ e₂ _))
  | Γ, .case a e₁ e₂, t => by
      simp only [lower2T]
      split
      · exact Keeps.trans (lower2A_keeps Γ a t) (Keeps.trans (lower2T_keeps _ e₁ _) (lower2T_keeps _ e₂ _))
      · exact lower2A_keeps Γ a t
end

end VIRC
