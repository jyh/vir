/-
  O95 layer L5, Lean arm (LV8-MAP.md; STATUS 318): the named layer for DEFLATE over the library. `NT₅` is DEFLATE's own `NT`
  (deflate/VIRDeflate/Step.lean) lifted whole by ι, plus ONE former for a lending call:
    `callK x c τ f a w e`  ≡  let x : τ, c ⇐ f a [w] in e    (one capability lent and handed back, L5-E1's call)
  An unchanged mode is `lift t`, compiled to `ιE (t.c Γ)`, so its L2 lemmas carry by CE (LV3) and nothing about it is re-proved.
-/
import VIRL5.Embed5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

inductive NT₅ where
  | lift (t : NT)
  | ret (a : NA)
  | op (x : String) (τ : Ty₂) (o : Op) (as : List NA) (e : NT₅)
  | ite (a : NA) (e₁ e₂ : NT₅)
  | letE (x : String) (τ : Ty₂) (e₁ e₂ : NT₅)
  | callK (x c : String) (τ : Ty₂) (f : Atom₅) (a : NA) (w : String) (e : NT₅)

/-- Compile in scope Γ (innermost first). `letK` binds the handed-back capability at #0 and the result at #1. -/
def NT₅.c (Γ : List String) : NT₅ → Tm₅
  | .lift t => ιE (t.c Γ)
  | .ret a => .ret (ιA (a.c Γ))
  | .op x τ o as e => .letOp o (ιL (as.map (NA.c Γ))) (ιT τ) (e.c (x :: Γ))
  | .ite a e₁ e₂ => .ite (ιA (a.c Γ)) (e₁.c Γ) (e₂.c Γ)
  | .letE x τ e₁ e₂ => .letE (ιT τ) (e₁.c Γ) (e₂.c (x :: Γ))
  | .callK x c τ f a w e => .letK (ιT τ) 1 (.appK f (ιA (a.c Γ)) [.var (Γ.idxOf w)]) (e.c (c :: x :: Γ))

/-- A lifted term compiles to the embedding of DEFLATE's own compiled term. -/
theorem NT₅.c_lift (Γ : List String) (t : NT) : (NT₅.lift t).c Γ = ιE (t.c Γ) := rfl

end VIRL5
