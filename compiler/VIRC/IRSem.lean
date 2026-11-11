/-
  O95 compiler, stage S1: the IR's semantics, a deterministic step FUNCTION over (state, L2 store). The store and its four
  operations are L2's own (`opStep`), so S1 cannot disagree with ⟶₂ about memory.
-/
import VIRC.IR

namespace VIRC
open VIRL1 VIRL2

def Val.asConst : Val → Option VIRL2.Const
  | .const c => some c
  | _ => none

mutual
/-- Operand evaluation in an environment: L1's ⟨a⟩ with the substitution replaced by a lookup. -/
def Opd.eval (ρ : List Val) : Opd → Option Val
  | .var n => ρ[n]?
  | .const c => some (.const c)
  | .prim p os => (Opd.evalL ρ os).bind fun ws => (ws.mapM Val.asConst).bind fun cs => (pInterp p cs).map .const
  | .code b c => some (.code b c)
  | .pair o₁ o₂ => (Opd.eval ρ o₁).bind fun v₁ => (Opd.eval ρ o₂).map fun v₂ => .pair v₁ v₂
  | .fst o => (Opd.eval ρ o).bind fun v => match v with
    | .pair v₁ _ => some v₁
    | _ => none
  | .snd o => (Opd.eval ρ o).bind fun v => match v with
    | .pair _ v₂ => some v₂
    | _ => none
  | .inl o => (Opd.eval ρ o).map .inl
  | .inr o => (Opd.eval ρ o).map .inr
def Opd.evalL (ρ : List Val) : List Opd → Option (List Val)
  | [] => some []
  | o :: os => (Opd.eval ρ o).bind fun v => (Opd.evalL ρ os).map (v :: ·)
end

/-- An O₂ operation on IR values: its arguments must be constants, and L2's `opStep` does the rest. -/
def opIR (op : VIRL2.Op) (ws : List Val) (σ : Store) : Option (Val × Store) :=
  (ws.mapM Val.asConst).bind fun cs => (opStep op (cs.map Atom.const) σ).map fun r =>
    (match r.1 with
     | .const c => Val.const c
     | _ => Val.junk, r.2)

/-- One IR step. -/
def stepIR : St × Store → Option (St × Store)
  | (.run (.ret o) ρ [], σ) => (Opd.eval ρ o).map fun v => (.done v, σ)
  | (.run (.ret o) ρ ((c, ρ') :: k), σ) => (Opd.eval ρ o).map fun v => (.run c (v :: ρ') k, σ)
  | (.run (.letE c₁ c₂) ρ k, σ) => some (.run c₁ ρ ((c₂, ρ) :: k), σ)
  | (.run (.letOp op os c) ρ k, σ) =>
      (Opd.evalL ρ os).bind fun ws => (opIR op ws σ).map fun r => (.run c (r.1 :: ρ) k, r.2)
  | (.run (.app f x) ρ k, σ) =>
      match Opd.eval ρ f, Opd.eval ρ x with
      | some (.code false b), some v => some (.run b [v] k, σ)
      | some (.code true b), some v => some (.run b [v, .code true b] k, σ)
      | _, _ => none
  | (.run (.ite o c₁ c₂) ρ k, σ) =>
      match Opd.eval ρ o with
      | some (.const (.bool true)) => some (.run c₁ ρ k, σ)
      | some (.const (.bool false)) => some (.run c₂ ρ k, σ)
      | _ => none
  | (.run (.case o c₁ c₂) ρ k, σ) =>
      match Opd.eval ρ o with
      | some (.inl v) => some (.run c₁ (v :: ρ) k, σ)
      | some (.inr v) => some (.run c₂ (v :: ρ) k, σ)
      | _ => none
  | (.done _, _) => none

/-- n IR steps. -/
inductive IRN : Nat → St × Store → St × Store → Prop where
  | refl (s) : IRN 0 s s
  | step {n s s' s''} : stepIR s = some s' → IRN n s' s'' → IRN (n + 1) s s''

theorem IRN.trans : ∀ {m n s s' s''}, IRN m s s' → IRN n s' s'' → IRN (m + n) s s''
  | _, _, _, _, _, .refl _, h => by simpa using h
  | _, _, _, _, _, .step h₁ h₂, h => by
      have := IRN.step h₁ (IRN.trans h₂ h); simpa [Nat.add_right_comm] using this

end VIRC
