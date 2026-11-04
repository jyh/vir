/-
  O95 layer L2, Lean arm. The acceptance programs M1–M5 (inputs/L2-programs.md), in de Bruijn form. Each O₂ operation is
  L1's effect binder `letOp`. This file grows per row: the run to the final configuration first, then typing and triples.
-/
import VIRL2.Typing2

namespace VIRL2
open VIRL1

abbrev ci (n : Int) : Atom₂ := .const (.int n)
abbrev vr (n : Nat) : Atom₂ := .var n

/-- M1: `let c:cap ← alloc(4) in let c1:cap ← store(c,2,7) in let v:int ← load(c1,2) in let u:unit ← free(c1) in ret v` -/
def M1 : Tm₂ :=
  .letOp .alloc [ci 4] tcap <|
  .letOp .store [vr 0, ci 2, ci 7] tcap <|
  .letOp .load [vr 0, ci 2] tint <|
  .letOp .free [vr 1] tunit <|
  .ret (vr 1)

/-- M2: two regions; a write to one leaves the other. -/
def M2 : Tm₂ :=
  .letOp .alloc [ci 2] tcap <|                 -- a        : #0
  .letOp .alloc [ci 2] tcap <|                 -- b #0, a #1
  .letOp .store [vr 1, ci 0, ci 5] tcap <|     -- a1 #0, b #1, a #2
  .letOp .store [vr 1, ci 0, ci 9] tcap <|     -- b1 #0, a1 #1
  .letOp .load [vr 1, ci 0] tint <|            -- x #0, b1 #1, a1 #2
  .letOp .free [vr 2] tunit <|                 -- u1 #0, x #1, b1 #2
  .letOp .free [vr 2] tunit <|                 -- u2 #0, u1 #1, x #2
  .ret (vr 2)

/-- M3: an out-of-bounds load. -/
def M3 : Tm₂ :=
  .letOp .alloc [ci 2] tcap <|
  .letOp .load [vr 0, ci 2] tint <|
  .letOp .free [vr 1] tunit <|
  .ret (vr 1)

/-- M4: a leak (no `free`). -/
def M4 : Tm₂ :=
  .letOp .alloc [ci 1] tcap <|
  .ret (ci 0)

theorem M1_run : (run₂ 20 (M1, Store.empty)).1 = .ret (ci 7) := rfl
theorem M2_run : (run₂ 20 (M2, Store.empty)).1 = .ret (ci 5) := rfl
theorem M3_stuck : (run₂ 20 (M3, Store.empty)).1 = .letOp .load [.const (.cap 0), ci 2] tint
    (.letOp .free [.const (.cap 0)] tunit (.ret (vr 1))) := rfl
theorem M4_run : (run₂ 20 (M4, Store.empty)).1 = .ret (ci 0) := rfl

/-! ## Typing (OBJECT-L2 §4). -/
theorem mask_empty_nil : Mask.empty ([] : List Bool) := by intro n; simp
theorem mask_empty_cons {Δ : List Bool} (h : Mask.empty Δ) : Mask.empty (false :: Δ) := by
  intro n; cases n with
  | zero => simp
  | succ n => simpa using h n

macro "mask_empty" : tactic => `(tactic| repeat (first | exact mask_empty_nil | apply mask_empty_cons))

theorem M1_typed : HasType₂ [] [] M1 tint := by
  unfold M1
  refine .alloc .int ?_
  refine .store rfl rfl .int .int ?_
  refine .load rfl rfl .int ?_
  refine .free (n := 1) rfl rfl ?_
  exact .ret (by simp [List.set]; mask_empty) (.var rfl rfl)

theorem M2_typed : HasType₂ [] [] M2 tint := by
  unfold M2
  refine .alloc .int ?_
  refine .alloc .int ?_
  refine .store (n := 1) rfl rfl .int .int ?_
  refine .store (n := 1) rfl rfl .int .int ?_
  refine .load (n := 1) rfl rfl .int ?_
  refine .free (n := 2) rfl rfl ?_
  refine .free (n := 2) rfl rfl ?_
  exact .ret (by simp [List.set]; mask_empty) (.var rfl rfl)

/-- M3 is WELL-TYPED: linearity does not check bounds (OBJECT-L2 §5, F8 ruled bounds-by-logic). -/
theorem M3_typed : HasType₂ [] [] M3 tint := by
  unfold M3
  refine .alloc .int ?_
  refine .load rfl rfl .int ?_
  refine .free (n := 1) rfl rfl ?_
  exact .ret (by simp [List.set]; mask_empty) (.var rfl rfl)

/-- M4 is ILL-TYPED: `ret 0` with the capability still in Δ (a leak). -/
theorem M4_untyped : ∀ τ, ¬ HasType₂ [] [] M4 τ := by
  intro τ h
  unfold M4 at h
  cases h with
  | alloc _ h =>
    cases h with
    | ret hΔ _ => exact hΔ 0 rfl

end VIRL2
