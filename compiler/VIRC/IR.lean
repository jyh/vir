/-
  O95 compiler, stage S1: the block IR (compiler/DECLARATIONS-S1.md).
  Operands keep L2's atom shapes, with variables read from an ENVIRONMENT (a register file, by de Bruijn index) instead of being
  substituted, and a function as CLOSED CODE (`Opd.code`): under C2 it captures nothing, so the code is its whole value, and S3
  gives each distinct code body an address (its label). `Code` is the program's control: a `letE` whose first part is not a
  `ret` PUSHES a frame, `app` CALLS (in tail position it is a jump: no frame), `ite`/`case` BRANCH, `letOp` is one store
  instruction. Types are erased: nothing in ⟶₂ reads them.
  Values become 64-bit words at S2, not here: S1 changes CONTROL and leaves REPRESENTATION alone.
-/
import VIRC.Fragment

namespace VIRC
open VIRL1 VIRL2

mutual
inductive Opd where
  | var (n : Nat)
  | const (c : VIRL2.Const)
  | prim (p : L1.Prim) (os : List Opd)
  | code (isFix : Bool) (body : Code)
  | pair (o₁ o₂ : Opd)
  | fst (o : Opd)
  | snd (o : Opd)
  | inl (o : Opd)
  | inr (o : Opd)
inductive Code where
  | ret (o : Opd)
  | letE (c₁ c₂ : Code)
  | letOp (op : VIRL2.Op) (os : List Opd) (k : Code)
  | app (f x : Opd)
  | ite (o : Opd) (c₁ c₂ : Code)
  | case (o : Opd) (c₁ c₂ : Code)
end

/-- IR values. `junk` is the image of a non-value atom under `valOf` (never produced by evaluation); no IR rule matches it. -/
inductive Val where
  | const (c : VIRL2.Const)
  | code (isFix : Bool) (body : Code)
  | pair (v₁ v₂ : Val)
  | inl (v : Val)
  | inr (v : Val)
  | junk

/-- A frame: the continuation's code and the environment it resumes in (the result is pushed as index 0). -/
abbrev Frame := Code × List Val

/-- IR machine states. A `run` state with no step is the IR's ONE fault state (amend-23 K-series: a fault is observable). -/
inductive St where
  | run (c : Code) (ρ : List Val) (k : List Frame)
  | done (v : Val)

end VIRC
