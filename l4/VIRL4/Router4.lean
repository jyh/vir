/-
  O95 layer L4, Lean arm (amend-21; H4 (a); erratum L4-E2 part (4), errata/L4-E2-N4.md). N4's terms: F₄ (L3's F with ONE critical
  section on the bucket region `b` behind the lock ℓb) and the two-router program `par (F₄[w₁]) (F₄[w₂])`, written with NAMES as
  L3 wrote F and compiled to de Bruijn `Tm₄` by `NT₄.c` (L3's named atoms `NA` reused through ι). N4-T: both typed by ⊢₄.
  Rows still owed on N4: N4-S (each side's triple) and N4-V (run_tokens₄ as a configuration invariant).
-/
import VIRL4.NoRace

namespace VIRL4
open VIRL1 VIRL2 VIRL3

/-- Named L4 terms: L3's forms plus `par` (two binders) and `ret ()`. -/
inductive NT₄ where
  | ret (a : NA)
  | retU
  | letE (x : String) (τ : Ty₄) (e₁ e₂ : NT₄)
  | op (x : String) (τ : Ty₄) (o : Op₄) (as : List NA) (e : NT₄)
  | ite (a : NA) (e₁ e₂ : NT₄)
  | par (x₁ x₂ : String) (τ₁ τ₂ : Ty₄) (e₁ e₂ e : NT₄)

def NA.c₄ (Γ : List String) (a : NA) : Atom₄ := ιA (a.c Γ)

/-- Compile in scope Γ (innermost first); `par` binds x₁ = #1, x₂ = #0 in its body (erratum L4-E1). -/
def NT₄.c (Γ : List String) : NT₄ → Tm₄
  | .ret a => .ret (NA.c₄ Γ a)
  | .retU => .ret unitv
  | .letE x τ e₁ e₂ => .letE τ (e₁.c Γ) (e₂.c (x :: Γ))
  | .op x τ o as e => .letOp o (as.map (NA.c₄ Γ)) τ (e.c (x :: Γ))
  | .ite a e₁ e₂ => .ite (NA.c₄ Γ a) (e₁.c Γ) (e₂.c Γ)
  | .par x₁ x₂ τ₁ τ₂ e₁ e₂ e => .par τ₁ τ₂ (e₁.c Γ) (e₂.c Γ) (e.c (x₂ :: x₁ :: Γ))

/-! The macros, as L3's (inputs/L3-programs.md), over NT₄. -/
def RD32₄ (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ :=
  let x0 := x ++ "0"; let x1 := x ++ "1"; let x2 := x ++ "2"; let x3 := x ++ "3"
  .op x0 t4int (.o2 .load) [.v w, .i (3 + o)] <|
  .op x1 t4int (.o2 .load) [.v w, .i (4 + o)] <|
  .op x2 t4int (.o2 .load) [.v w, .i (5 + o)] <|
  .op x3 t4int (.o2 .load) [.v w, .i (6 + o)] <|
  .letE x t4int (.ret (add (.v x0) (add (mul (.i 256) (.v x1))
      (add (mul (.i 65536) (.v x2)) (mul (.i 16777216) (.v x3)))))) k

def EXIT₄ (w : String) (c : Int) : NT₄ :=
  .op "w'" t4cap (.o2 .store) [.v w, .i 1, .i c] (.ret (.v "w'"))

def EMIT₄ (w : String) : NT₄ :=
  .op "w'" t4cap (.o2 .store) [.v w, .i 1, .i 0] <|
  .op "w''" t4cap (.o2 .store) [.v "w'", .i 2, .i 24] (.ret (.v "w''"))

/-- F₄ on the world named w, with the lock named "lb" (errata/L4-E2-N4.md, "F₄"). -/
def Fn₄ (w : String) : NT₄ :=
  .op "n" t4int (.o2 .load) [.v w, .i 0] <|
  .ite (le (.i 24) (.v "n"))
    (RD32₄ w 0 "magic" <| RD32₄ w 4 "sender" <| RD32₄ w 8 "topic" <|
      .op "a" t4int (.o2 .load) [.v w, add (.i A) (add (mul (.v "sender") (.i NTp)) (.v "topic"))] <|
      .op "b" t4cap .acquire [.v "lb"] <|
      .op "t" t4int (.o2 .load) [.v "b", .v "sender"] <|
      .ite (conj (eq (.v "magic") (.i MAGIC)) (conj (eq (.v "a") (.i 1)) (lt (.i 0) (.v "t"))))
        (.op "b1" t4cap (.o2 .store) [.v "b", .v "sender", sub (.v "t") (.i 1)] <|
          .op "r" t4unit .release [.v "lb", .v "b1"] (EMIT₄ w))
        (.op "r" t4unit .release [.v "lb", .v "b"] (EXIT₄ w 2)))
    (EXIT₄ w 1)

/-- F₄ alone: free variables w : cap (#0), ℓb : lock (#1). -/
def F₄ : Tm₄ := (Fn₄ "w").c ["w", "lb"]

/-- N4 (errata/L4-E2-N4.md): free variables w₂ (#0), w₁ (#1), ℓb (#2). -/
def N4n : NT₄ :=
  .par "w1'" "w2'" t4cap t4cap (Fn₄ "w1") (Fn₄ "w2") <|
  .op "u1" t4unit (.o2 .free) [.v "w1'"] <|
  .op "u2" t4unit (.o2 .free) [.v "w2'"] .retU

def N4 : Tm₄ := N4n.c ["w2", "w1", "lb"]

theorem mask_only_zero {Δ : List Bool} (h : Mask.empty Δ) : Mask.only (true :: Δ) 0 :=
  ⟨rfl, fun m hm => by
    cases m with
    | zero => exact absurd rfl hm
    | succ m => simpa using h m⟩

/-- ⊢₄ syntax-directed, for terms whose `let`s bind pure values (RD32's sum) and whose exits return the world. -/
macro "l4ty'" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl | exact Or.inl rfl
  | exact HasTypeA₄.int | exact HasTypeA₄.bool | exact HasTypeA₄.unit
  | exact HasTypeA₄.var rfl rfl
  | refine HasTypeA₄.prim ?_
  | exact HasTypeL₄.nil | refine HasTypeL₄.cons ?_ ?_
  | refine HasType₄.retCap rfl (mask_only_zero ?_)
  | refine HasType₄.ret ?_ ?_
  | refine HasType₄.letE (split_left_empty _) (Or.inr rfl) ?_ ?_
  | refine HasType₄.ite ?_ ?_ ?_
  | refine HasType₄.load rfl rfl ?_ ?_
  | refine HasType₄.store rfl rfl ?_ ?_ ?_
  | refine HasType₄.free rfl rfl ?_
  | refine HasType₄.acquire ?_ ?_
  | refine HasType₄.release ?_ rfl rfl ?_))

set_option maxRecDepth 4000 in
/-- N4-T, F₄'s half: F₄ is typed `cap` in (w : cap, ℓb : lock) with Δ = {w}. -/
theorem F₄_typed : HasType₄ [t4cap, t4lock] [true, false] F₄ t4cap := by
  simp only [F₄, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.c, NA.c₄, NA.c, ιA, ιL, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
  l4ty'

set_option maxRecDepth 4000 in
/-- N4-T: N4 is typed `unit` in (w₂ : cap, w₁ : cap, ℓb : lock) with Δ = {w₁, w₂}: par gives w₁ to the left side, w₂ to the right,
  nothing to the body, which frees the two returned worlds. -/
theorem N4_typed : HasType₄ [t4cap, t4cap, t4lock] [true, true, false] N4 t4unit := by
  simp only [N4, N4n, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.c, NA.c₄, NA.c, ιA, ιL, add, sub, mul, le, lt, eq, conj, List.map,
    List.idxOf, List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd,
    Nat.zero_add]
  refine HasType₄.par (Δ₁ := [false, true, false]) (Δ' := [true, false, false]) (Δ₂ := [true, false, false])
    (Δ₀ := [false, false, false]) (Split.right (Split.left (Split.none Split.nil))) (Split.left (Split.none (Split.none Split.nil)))
    (Or.inl rfl) (Or.inl rfl) ?_ ?_ ?_ <;> l4ty'

end VIRL4
