/-
  O95 compiler, stage S2: the lowering to word code, indexed by the SOURCE term (DECLARATIONS-S2 "Added"), with Γ the typing
  context (caller parameters first). Types come from `inferA`, which every derivation fixes (`inferT_sound`). A λ/fix atom gets a
  LABEL: the table's next index is reserved before its body is compiled, so nested functions take the labels after it, and
  the body is written into its slot afterwards. Every label is therefore fixed at the moment its atom is reached.
  A body is compiled under its OWN context ([τ] for λ, [τ₁, τ₁ → τ₂] for fix), never the enclosing one. C2 makes it closed, so
  the offsets would agree either way. What this buys is that a body's code does not depend on WHERE its atom occurs, which is
  what the code-value relation in the simulation needs.
  A shape that ⊢₂ or `Fragment2.ok` rules out lowers to a harmless placeholder. The S2 theorem quantifies only over
  accepted, typed programs.
-/
import VIRC.Fragment2

namespace VIRC
open VIRL1 VIRL2

def primW : L1.Prim → List WOpd → WOpd
  | .add, [a, b] => .arith .add a b
  | .sub, [a, b] => .arith .sub a b
  | .mul, [a, b] => .arith .mul a b
  | .lt, [a, b] => .arith .lt a b
  | .le, [a, b] => .arith .le a b
  | .eq, [a, b] => .arith .eq a b
  | .max, [a, b] => .arith .max a b
  | .and, [a, b] => .arith .band a b
  | .or, [a, b] => .arith .bor a b
  | .not, [a] => .bnot a
  | _, _ => .imm []

def placeholder : WCode := .ret (.imm [])

/-- The instruction for an O₂ operation, given its lowered operands and its lowered continuation. S2-A (a): only `load` and
`store`. The capability is a VARIABLE (⊢₂), read by its offset. -/
def opCode (Γ : Ctx S₂) : VIRL2.Op → List Atom₂ → List WOpd → WCode → WCode
  | .load, [.var n, _], [_, oi], k => .load (offset Γ n) oi k
  | .store, [.var n, _, _], [_, oi, ov], k => .store (offset Γ n) oi ov k
  | _, _, _, _ => placeholder

mutual
def lower2A (Γ : Ctx S₂) : Atom₂ → Table → WOpd × Table
  | .var n, t => (varSlice Γ n, t)
  | .const (.int n), t => (.imm [BitVec.ofInt 64 n], t)
  | .const (.bool b), t => (.imm [boolW b], t)
  | .const .unit, t => (.imm [0], t)
  | .const (.cap _), t => (.imm [], t)
  | .prim p as, t => let r := lower2L Γ as t; (primW p r.1, r.2)
  | .lam τ e, t =>
      let r := lower2T [τ] e (t ++ [(false, placeholder)])
      (.imm [BitVec.ofNat 64 t.length], r.2.set t.length (false, r.1))
  | .fix τ₁ τ₂ e, t =>
      let r := lower2T [τ₁, .arr τ₁ τ₂] e (t ++ [(true, placeholder)])
      (.imm [BitVec.ofNat 64 t.length], r.2.set t.length (true, r.1))
  | .pair a₁ a₂, t => let r₁ := lower2A Γ a₁ t; let r₂ := lower2A Γ a₂ r₁.2; (.cat r₁.1 r₂.1, r₂.2)
  | .fst a, t => let r := lower2A Γ a t
      match inferA Γ a with
      | some (.prod t₁ _) => (.take (size t₁) r.1, r.2)
      | _ => (r.1, r.2)
  | .snd a, t => let r := lower2A Γ a t
      match inferA Γ a with
      | some (.prod t₁ _) => (.drop (size t₁) r.1, r.2)
      | _ => (r.1, r.2)
  | .inl τ₂ a, t => let r := lower2A Γ a t
      match inferA Γ a with
      | some τ₁ => (.tag 0 (max (size τ₁) (size τ₂) - size τ₁) r.1, r.2)
      | none => (r.1, r.2)
  | .inr τ₁ a, t => let r := lower2A Γ a t
      match inferA Γ a with
      | some τ₂ => (.tag 1 (max (size τ₁) (size τ₂) - size τ₂) r.1, r.2)
      | none => (r.1, r.2)
def lower2L (Γ : Ctx S₂) : List Atom₂ → Table → List WOpd × Table
  | [], t => ([], t)
  | a :: as, t => let r := lower2A Γ a t; let rs := lower2L Γ as r.2; (r.1 :: rs.1, rs.2)
def lower2T (Γ : Ctx S₂) : Tm₂ → Table → WCode × Table
  | .ret a, t => let r := lower2A Γ a t; (.ret r.1, r.2)
  | .letE τ e₁ e₂, t => let r₁ := lower2T Γ e₁ t; let r₂ := lower2T (τ :: Γ) e₂ r₁.2; (.letE r₁.1 r₂.1, r₂.2)
  | .letOp o as τ e, t =>
      let rs := lower2L Γ as t; let k := lower2T (τ :: Γ) e rs.2; (opCode Γ o as rs.1 k.1, k.2)
  | .app a₁ a₂, t => let r₁ := lower2A Γ a₁ t; let r₂ := lower2A Γ a₂ r₁.2; (.app r₁.1 r₂.1, r₂.2)
  | .ite a e₁ e₂, t =>
      let r := lower2A Γ a t; let r₁ := lower2T Γ e₁ r.2; let r₂ := lower2T Γ e₂ r₁.2; (.ite r.1 r₁.1 r₂.1, r₂.2)
  | .case a e₁ e₂, t => let r := lower2A Γ a t
      match inferA Γ a with
      | some (.sum t₁ t₂) =>
          let r₁ := lower2T (t₁ :: Γ) e₁ r.2; let r₂ := lower2T (t₂ :: Γ) e₂ r₁.2
          (.case r.1 (size t₁) (size t₂) r₁.1 r₂.1, r₂.2)
      | _ => (placeholder, r.2)
end

/-- Stage S2, from the source: `none` = REJECTED (C2 or S2's predicate). Γ₀ is the caller's parameter context. -/
def compile2 (Γ₀ : Ctx S₂) (e : Tm₂) : Option (WCode × Table) :=
  if Fragment2.ok e then some (lower2T Γ₀ e []) else none

/-! ## Concrete runs (evaluation checks, kernel-reduced): the compiled code computes what ⟶₂ computes, and its two exits fire. -/
def runW (tbl : Table) : Nat → WSt × WMem → WSt
  | 0, s => s.1
  | n + 1, s => match stepW tbl s with
    | some s' => runW tbl n s'
    | none => s.1

def WSt.isDone (ws : List W) : WSt → Bool
  | .done xs => decide (xs = ws)
  | _ => false

def WSt.isOvf : WSt → Bool
  | .ovf => true
  | _ => false

def WSt.isFault : WSt → Bool
  | .fault => true
  | _ => false

def runProg (Γ₀ : Ctx S₂) (e : Tm₂) (ρ : List W) (m : WMem) (fuel : Nat) : WSt :=
  let r := lower2T Γ₀ e []
  runW r.2 fuel (.run r.1 ρ [], m)

private def i (n : Int) : Atom₂ := .const (.int n)
private def add (a b : Atom₂) : Atom₂ := .prim .add [a, b]
private def mul (a b : Atom₂) : Atom₂ := .prim .mul [a, b]

/-- let x = 3 + 4 in (x, x * 2)  ⇒  [7, 14] -/
theorem run_pair : (runProg [] (.letE tint (.ret (add (i 3) (i 4))) (.ret (.pair (.var 0) (mul (.var 0) (i 2)))))
    [] (fun _ => 0) 10).isDone [7, 14] = true := by decide

/-- (λx:int. x + 1) 5  ⇒  [6]  (a call through the code table) -/
theorem run_call : (runProg [] (.app (.lam tint (.ret (add (.var 0) (i 1)))) (i 5)) [] (fun _ => 0) 10).isDone [6] = true := by
  decide

/-- case inr[int] true of inl x ⇒ x | inr b ⇒ (if b then 1 else 2)  ⇒  [1] -/
theorem run_case : (runProg [] (.case (.inr tint (.const (.bool true))) (.ret (.var 0))
    (.ite (.var 0) (.ret (i 1)) (.ret (i 2)))) [] (fun _ => 0) 10).isDone [1] = true := by decide

/-- 2⁶² · 2 leaves the range: the OVERFLOW exit (C4 (b)), never a wrapped value. -/
theorem run_ovf : (runProg [] (.ret (mul (i (2 ^ 62)) (i 2))) [] (fun _ => 0) 10).isOvf = true := by decide

/-- load(⟨p⟩, 3) on a 2-cell region: the FAULT exit. The caller's capability is the two words (base 64, length 2). -/
theorem run_fault : (runProg [tcap] (.letOp .load [.var 0, i 3] tint (.ret (.var 0))) [64, 2] (fun _ => 0) 10).isFault = true := by
  decide

/-- load(⟨p⟩, 1) on a 2-cell region whose cell 1 holds 42: [42]. -/
theorem run_load : (runProg [tcap] (.letOp .load [.var 0, i 1] tint (.ret (.var 0))) [64, 2]
    (fun a => if a = 72 then 42 else 0) 10).isDone [42] = true := by decide

end VIRC
