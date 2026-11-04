/-
  O95 layer L1, Lean arm: the THREE-SORTED STRUCTURAL INDUCTION rule (PREDICTIONS-amend-19, the Captain's ruling at the
  11-03 afternoon council, minute §E ①). An L1 ADDENDUM: this file is NEW and no other file of `VIRL1` is edited (amend-19 I1);
  it is built as its own target and is not imported by `VIRL1.lean`.

  The statement is amend-19's "The rule" block in this arm's representation: depth = de Bruijn depth, wf = `Atom.wf`/`Tm.wf`.
  Declared, per amend-19:
  - A2: this arm has ONE literal form, `const c` (n ∈ ℤ, true and false are all constants of the signature), so ONE premise.
  - A3: ONE premise for all of P, its IH over the argument list.
  - E3 is present (`letOp`), vacuous on L1's programs (O = ∅ in L1's signature).
  - W3 premises (I6): `prod`, `sum` (types); `pair`, `fst`, `snd`, `inl`, `inr` (atoms); `case` (expressions), marked X1–X8.
-/
import VIRL1.Syntax

namespace VIRL1.MutantIndSameDepth

variable {S : Sig}

section Induction

-- the mutual block takes every premise as a parameter; Lean warns that each theorem alone uses only some of them
set_option linter.unusedSectionVars false

variable (Pτ : Ty S.B → Prop) (Pa : Nat → Atom S → Prop) (Pe : Nat → Tm S → Prop)
  (T1 : ∀ b, Pτ (.base b))
  (T2 : ∀ τ₁ τ₂, Pτ τ₁ → Pτ τ₂ → Pτ (.arr τ₁ τ₂))
  (A1 : ∀ n m, m < n → Pa n (.var m))
  (A2 : ∀ n c, Pa n (.const c))
  (A3 : ∀ n p as, (∀ a ∈ as, Pa n a) → Pa n (.prim p as))
  (A4 : ∀ n τ e, Pτ τ → Pe n e → Pa n (.lam τ e))
  (A5 : ∀ n τ₁ τ₂ e, Pτ τ₁ → Pτ τ₂ → Pe (n + 2) e → Pa n (.fix τ₁ τ₂ e))
  (E1 : ∀ n a, Pa n a → Pe n (.ret a))
  (E2 : ∀ n τ e₁ e₂, Pτ τ → Pe n e₁ → Pe (n + 1) e₂ → Pe n (.letE τ e₁ e₂))
  (E3 : ∀ n o as τ e, (∀ a ∈ as, Pa n a) → Pτ τ → Pe (n + 1) e → Pe n (.letOp o as τ e))
  (E4 : ∀ n a₁ a₂, Pa n a₁ → Pa n a₂ → Pe n (.app a₁ a₂))
  (E5 : ∀ n a e₁ e₂, Pa n a → Pe n e₁ → Pe n e₂ → Pe n (.ite a e₁ e₂))
  -- W3 extensions (amend-19 I6)
  (X1 : ∀ τ₁ τ₂, Pτ τ₁ → Pτ τ₂ → Pτ (.prod τ₁ τ₂))
  (X2 : ∀ τ₁ τ₂, Pτ τ₁ → Pτ τ₂ → Pτ (.sum τ₁ τ₂))
  (X3 : ∀ n a₁ a₂, Pa n a₁ → Pa n a₂ → Pa n (.pair a₁ a₂))
  (X4 : ∀ n a, Pa n a → Pa n (.fst a))
  (X5 : ∀ n a, Pa n a → Pa n (.snd a))
  (X6 : ∀ n τ a, Pτ τ → Pa n a → Pa n (.inl τ a))
  (X7 : ∀ n τ a, Pτ τ → Pa n a → Pa n (.inr τ a))
  (X8 : ∀ n a e₁ e₂, Pa n a → Pe (n + 1) e₁ → Pe (n + 1) e₂ → Pe n (.case a e₁ e₂))

include T1 T2 X1 X2 in
theorem ind_ty : ∀ τ, Pτ τ
  | .base b => T1 b
  | .arr τ₁ τ₂ => T2 _ _ (ind_ty τ₁) (ind_ty τ₂)
  | .prod τ₁ τ₂ => X1 _ _ (ind_ty τ₁) (ind_ty τ₂)
  | .sum τ₁ τ₂ => X2 _ _ (ind_ty τ₁) (ind_ty τ₂)

include T1 T2 A1 A2 A3 A4 A5 E1 E2 E3 E4 E5 X1 X2 X3 X4 X5 X6 X7 X8 in
mutual
theorem ind_atom : ∀ n (a : Atom S), Atom.wf n a → Pa n a
  | n, .var m, h => A1 n m h
  | n, .const c, _ => A2 n c
  | n, .prim p as, h => A3 n p as (ind_atoms n as h)
  | n, .lam τ e, h => A4 n τ e (ind_ty Pτ T1 T2 X1 X2 τ) (ind_tm (n + 1) e h)
  | n, .fix τ₁ τ₂ e, h => A5 n τ₁ τ₂ e (ind_ty Pτ T1 T2 X1 X2 τ₁) (ind_ty Pτ T1 T2 X1 X2 τ₂) (ind_tm (n + 2) e h)
  | n, .pair a₁ a₂, h => X3 n a₁ a₂ (ind_atom n a₁ h.1) (ind_atom n a₂ h.2)
  | n, .fst a, h => X4 n a (ind_atom n a h)
  | n, .snd a, h => X5 n a (ind_atom n a h)
  | n, .inl τ a, h => X6 n τ a (ind_ty Pτ T1 T2 X1 X2 τ) (ind_atom n a h)
  | n, .inr τ a, h => X7 n τ a (ind_ty Pτ T1 T2 X1 X2 τ) (ind_atom n a h)
theorem ind_atoms : ∀ n (as : List (Atom S)), Atom.wfL n as → ∀ a ∈ as, Pa n a
  | _, [], _, _, ha => nomatch ha
  | n, b :: bs, h, a, ha => (List.mem_cons.1 ha).elim (fun e => e ▸ ind_atom n b h.1) (ind_atoms n bs h.2 a)
theorem ind_tm : ∀ n (e : Tm S), Tm.wf n e → Pe n e
  | n, .ret a, h => E1 n a (ind_atom n a h)
  | n, .letE τ e₁ e₂, h => E2 n τ e₁ e₂ (ind_ty Pτ T1 T2 X1 X2 τ) (ind_tm n e₁ h.1) (ind_tm (n + 1) e₂ h.2)
  | n, .letOp o as τ e, h => E3 n o as τ e (ind_atoms n as h.1) (ind_ty Pτ T1 T2 X1 X2 τ) (ind_tm (n + 1) e h.2)
  | n, .app a₁ a₂, h => E4 n a₁ a₂ (ind_atom n a₁ h.1) (ind_atom n a₂ h.2)
  | n, .ite a e₁ e₂, h => E5 n a e₁ e₂ (ind_atom n a h.1) (ind_tm n e₁ h.2.1) (ind_tm n e₂ h.2.2)
  | n, .case a e₁ e₂, h => X8 n a e₁ e₂ (ind_atom n a h.1) (ind_tm (n + 1) e₁ h.2.1) (ind_tm (n + 1) e₂ h.2.2)
end

include T1 T2 A1 A2 A3 A4 A5 E1 E2 E3 E4 E5 X1 X2 X3 X4 X5 X6 X7 X8 in
/-- amend-19's rule: the three conclusions, at every depth. -/
theorem three_sorted_induction :
    (∀ τ, Pτ τ) ∧ (∀ n (a : Atom S), Atom.wf n a → Pa n a) ∧ (∀ n (e : Tm S), Tm.wf n e → Pe n e) :=
  ⟨ind_ty Pτ T1 T2 X1 X2,
   ind_atom Pτ Pa Pe T1 T2 A1 A2 A3 A4 A5 E1 E2 E3 E4 E5 X1 X2 X3 X4 X5 X6 X7 X8,
   ind_tm Pτ Pa Pe T1 T2 A1 A2 A3 A4 A5 E1 E2 E3 E4 E5 X1 X2 X3 X4 X5 X6 X7 X8⟩

end Induction

end VIRL1.MutantIndSameDepth
