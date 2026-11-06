/-
  O95 layer L4, Lean arm (amend-21). The programs N1–N3 as de Bruijn Tm₄, read under errata L4-E1 (par binds its two results)
  and L4-E2 (N1 releases c2; INC ends `let u ← release in ret u`; N3's fixed term). N2 is "N1 with newlock removed and both sides
  given c1 directly" (inputs §3): each side loads and stores c1 itself and returns it. Its refutation is the typing row.
  Each derivation is built by `l4ty`, which applies ⊢₄'s rules syntax-directed.
-/
import VIRL4.Typing4

namespace VIRL4
open VIRL1 VIRL2 VIRL3

abbrev c4 (n : Int) : Atom₄ := .const (.c2 (.int n))
abbrev v4 (n : Nat) : Atom₄ := .var n
def padd (a b : Atom₄) : Atom₄ := .prim .add [a, b]

/-- INC ℓ, with ℓ at index k: `let d ← acquire(ℓ) in let y ← load(d,0) in let d1 ← store(d,0,add(y,1)) in let u ← release(ℓ,d1) in ret u`. -/
def INC (k : Nat) : Tm₄ :=
  .letOp .acquire [v4 k] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .letOp .release [v4 (k + 3), v4 0] t4unit <|
  .ret (v4 0)

/-- N1 (L4-E1, L4-E2): alloc · store 0 · newlock · par (INC) (INC) · acquire · load · release · ret x. -/
def N1 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .letOp .newlock [v4 0] t4lock <|
  .par t4unit t4unit (INC 0) (INC 0) <|
  .letOp .acquire [v4 2] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp .release [v4 4, v4 1] t4unit <|
  .ret (v4 1)

/-- N2's side: c1 at index 0, used directly (no lock): load, store, return the capability. -/
def SIDE : Tm₄ :=
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .ret (v4 0)

/-- N2: N1 with newlock removed, both sides given c1; the body frees both results. -/
def N2 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .par t4cap t4cap SIDE SIDE <|
  .letOp (.o2 .free) [v4 0] t4unit <|
  .letOp (.o2 .free) [v4 2] t4unit <|
  .ret (c4 0)

/-- N3 (L4-E2): a release whose cell holds −1 under inv(v) := v ≥ 0. -/
def N3 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .letOp .newlock [v4 0] t4lock <|
  .letOp .acquire [v4 0] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 (-1)] t4cap <|
  .letOp .release [v4 2, v4 0] t4unit <|
  .ret (v4 0)

theorem split_none_all : ∀ Δ : List Bool, (∀ b ∈ Δ, b = false) → Split Δ Δ Δ
  | [], _ => .nil
  | b :: Δ, h => by
      have hb := h b (by simp); subst hb
      exact .none (split_none_all Δ (fun x hx => h x (by simp [hx])))

/-- `par` is applied only where every capability is already consumed (all-`none` splits), which is N1's case. -/
macro "l4ty" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl
  | exact HasTypeA₄.int | exact HasTypeA₄.bool | exact HasTypeA₄.unit
  | exact HasTypeA₄.var rfl rfl
  | refine HasTypeA₄.prim ?_
  | exact HasTypeL₄.nil | refine HasTypeL₄.cons ?_ ?_
  | refine HasType₄.ret ?_ ?_
  | refine HasType₄.alloc ?_ ?_
  | refine HasType₄.load rfl rfl ?_ ?_
  | refine HasType₄.store rfl rfl ?_ ?_ ?_
  | refine HasType₄.free rfl rfl ?_
  | refine HasType₄.newlock rfl rfl ?_
  | refine HasType₄.acquire ?_ ?_
  | refine HasType₄.release ?_ rfl rfl ?_
  | refine HasType₄.par (split_none_all _ (by decide)) (split_none_all _ (by decide)) (Or.inr rfl) (Or.inr rfl) ?_ ?_ ?_))

/-- N1-T. -/
theorem N1_typed : HasType₄ [] [] N1 t4int := by
  simp only [N1, INC, padd]
  l4ty

/-- N3-T: TYPED (⊢₄ does not read invariants). -/
theorem N3_typed : HasType₄ [] [] N3 t4unit := by
  simp only [N3]
  l4ty

/-- N2's row: ILL-TYPED at every type. Both sides open with a load of c1, so each needs c1 in its mask; the split gives it to one. -/
theorem N2_untyped : ∀ τ, ¬ HasType₄ [] [] N2 τ := by
  intro τ h
  simp only [N2, SIDE, padd] at h
  cases h with
  | alloc _ h =>
  cases h with
  | store _ _ _ _ h =>
  cases h with
  | par s₁ s₂ _ _ h₁ h₂ _ =>
  cases h₁ with
  | load _ hΔ₁ _ _ =>
  cases h₂ with
  | load _ hΔ₂ _ _ =>
  cases s₁ <;> cases s₂ <;> simp_all

end VIRL4
