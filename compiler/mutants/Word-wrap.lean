/-
  O95 compiler, stage S2: the WORD MACHINE (compiler/DECLARATIONS-S2.md). Every value is a list of 64-bit words, sized by its
  L2 type (S2-R (a)). The environment is ONE flat word list, innermost binder first, so a variable is a SLICE (offset, length).
  A capability is two words, base address and length in cells (S2-C), and a cell is one 8-byte word at `base + 8·i` (S2-M (a)).
  Memory is word-granular (`W → W`, read at cell addresses). S3 reads each word as 8 bytes of x86lean's byte memory.
  THREE ENDINGS: `done`; `fault` (an index out of its region's bounds: the ONE fault exit); `ovf` (an int left
  [−2⁶³, 2⁶³): C4 (b)'s second exit). Code values are LABELS into a code table, which is S3's address assignment in miniature.
-/
import VIRC.Infer

namespace VIRC

abbrev W := BitVec 64

/-- Integer and boolean operators on one-word operands (L1's P, plus checked arithmetic). -/
inductive AOp | add | sub | mul | lt | le | eq | max | band | bor

inductive WOpd where
  | slice (off len : Nat)
  | imm (ws : List W)
  | arith (op : AOp) (a b : WOpd)
  | bnot (a : WOpd)
  | cat (a b : WOpd)
  | take (n : Nat) (a : WOpd)
  | drop (n : Nat) (a : WOpd)
  | tag (t : W) (pad : Nat) (a : WOpd)   -- a sum value: [t] ++ a ++ pad zero words

inductive WCode where
  | ret (o : WOpd)
  | letE (c₁ c₂ : WCode)
  | load (capOff : Nat) (idx : WOpd) (k : WCode)
  | store (capOff : Nat) (idx v : WOpd) (k : WCode)
  | app (f x : WOpd)
  | ite (o : WOpd) (c₁ c₂ : WCode)
  | case (o : WOpd) (n₁ n₂ : Nat) (c₁ c₂ : WCode)

/-- The result of evaluating an operand: words, an OVERFLOW, or BAD (a shape no compiled typed program produces). -/
inductive WRes | ok (ws : List W) | ovf | bad

def inRange (n : Int) : Bool := decide (-2 ^ 63 ≤ n ∧ n < 2 ^ 63)

/-- A checked integer result. -/
def chk (n : Int) : WRes := .ok [BitVec.ofInt 64 n]   -- MUTANT: C4 (b) removed, arithmetic wraps

def boolW (b : Bool) : W := if b then 1 else 0

def AOp.apply : AOp → W → W → WRes
  | .add, x, y => chk (x.toInt + y.toInt)
  | .sub, x, y => chk (x.toInt - y.toInt)
  | .mul, x, y => chk (x.toInt * y.toInt)
  | .lt, x, y => .ok [boolW (decide (x.toInt < y.toInt))]
  | .le, x, y => .ok [boolW (decide (x.toInt ≤ y.toInt))]
  | .eq, x, y => .ok [boolW (decide (x = y))]
  | .max, x, y => .ok [if x.toInt ≤ y.toInt then y else x]
  | .band, x, y => .ok [x &&& y]
  | .bor, x, y => .ok [x ||| y]

def WRes.bind : WRes → (List W → WRes) → WRes
  | .ok ws, f => f ws
  | .ovf, _ => .ovf
  | .bad, _ => .bad

def evalW (ρ : List W) : WOpd → WRes
  | .slice off len => if off + len ≤ ρ.length then .ok ((ρ.drop off).take len) else .bad
  | .imm ws => .ok ws
  | .arith op a b => (evalW ρ a).bind fun xs => (evalW ρ b).bind fun ys => match xs, ys with
    | [x], [y] => op.apply x y
    | _, _ => .bad
  | .bnot a => (evalW ρ a).bind fun xs => match xs with
    | [x] => .ok [1 - x]
    | _ => .bad
  | .cat a b => (evalW ρ a).bind fun xs => (evalW ρ b).bind fun ys => .ok (xs ++ ys)
  | .take n a => (evalW ρ a).bind fun xs => .ok (xs.take n)
  | .drop n a => (evalW ρ a).bind fun xs => .ok (xs.drop n)
  | .tag t pad a => (evalW ρ a).bind fun xs => .ok (t :: xs ++ List.replicate pad 0)

/-- Word memory: the word at each cell address. -/
abbrev WMem := W → W

def cellAddr (base : W) (i : W) : W := base + 8 * i

inductive WSt where
  | run (c : WCode) (ρ : List W) (k : List (WCode × List W))
  | done (ws : List W)
  | fault
  | ovf

/-- The code table: label ↦ (is it a fix, its body). -/
abbrev Table := List (Bool × WCode)

/-- One word-machine step. `none` = no step: an ending (`done`, `fault`, `ovf`) or a BAD shape. -/
def stepW (tbl : Table) : WSt × WMem → Option (WSt × WMem)
  | (.run (.ret o) ρ k, m) => match evalW ρ o, k with
    | .ok ws, [] => some (.done ws, m)
    | .ok ws, (c, ρ') :: k' => some (.run c (ws ++ ρ') k', m)
    | .ovf, _ => some (.ovf, m)
    | .bad, _ => none
  | (.run (.letE c₁ c₂) ρ k, m) => some (.run c₁ ρ ((c₂, ρ) :: k), m)
  | (.run (.load off idx c) ρ k, m) => match ρ[off]?, ρ[off + 1]?, evalW ρ idx with
    | some base, some len, .ok [i] =>
        if 0 ≤ i.toInt ∧ i.toInt < len.toInt then some (.run c (m (cellAddr base i) :: ρ) k, m)
        else some (.fault, m)
    | _, _, .ovf => some (.ovf, m)
    | _, _, _ => none
  | (.run (.store off idx v c) ρ k, m) => match ρ[off]?, ρ[off + 1]?, evalW ρ idx, evalW ρ v with
    | some base, some len, .ok [i], .ok [x] =>
        if 0 ≤ i.toInt ∧ i.toInt < len.toInt then
          some (.run c (base :: len :: ρ) k, Function.update m (cellAddr base i) x)
        else some (.fault, m)
    | _, _, .ovf, _ => some (.ovf, m)
    | _, _, _, .ovf => some (.ovf, m)
    | _, _, _, _ => none
  | (.run (.app f x) ρ k, m) => match evalW ρ f, evalW ρ x with
    | .ok [l], .ok ws => match tbl[l.toNat]? with
      | some (false, b) => some (.run b ws k, m)
      | some (true, b) => some (.run b (ws ++ [l]) k, m)
      | none => none
    | .ovf, _ => some (.ovf, m)
    | _, .ovf => some (.ovf, m)
    | _, _ => none
  | (.run (.ite o c₁ c₂) ρ k, m) => match evalW ρ o with
    | .ok [b] => if b = 1 then some (.run c₁ ρ k, m) else if b = 0 then some (.run c₂ ρ k, m) else none
    | .ovf => some (.ovf, m)
    | _ => none
  | (.run (.case o n₁ n₂ c₁ c₂) ρ k, m) => match evalW ρ o with
    | .ok (t :: ws) =>
        if t = 0 then some (.run c₁ (ws.take n₁ ++ ρ) k, m)
        else if t = 1 then some (.run c₂ (ws.take n₂ ++ ρ) k, m) else none
    | .ovf => some (.ovf, m)
    | _ => none
  | (.done _, _) | (.fault, _) | (.ovf, _) => none

/-- n word-machine steps. -/
inductive WN (tbl : Table) : Nat → WSt × WMem → WSt × WMem → Prop where
  | refl (s) : WN tbl 0 s s
  | step {n s s' s''} : stepW tbl s = some s' → WN tbl n s' s'' → WN tbl (n + 1) s s''

end VIRC
