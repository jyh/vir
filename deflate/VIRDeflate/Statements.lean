/-
OBJECT-DEFLATE under X1 (a): the initial world and the X3 (a) statements (DECLARATIONS-DEFLATE.md S-5, with the layout of
S-1, S-7, S-8, S-9, S-12, S-13 and S-14). STATUS-vir 293: the statements are written HERE, as `Prop` definitions, BEFORE any
proof of them. D3 and D7 are scored on `SafetyStmt`; correctness is `CorrectStmt`.
-/
import VIRDeflate.Dispatch

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## The initial world: a function of (b, OUTMAX, the reading) alone -/

/-- `fill` with a value per cell: cells p … p + k − 1 get g 0 … g (k − 1). -/
def fillF (h : Finmap (fun _ : Int => Int)) (p : Int) (g : Int → Int) : Nat → Finmap (fun _ : Int => Int)
  | 0 => h
  | k + 1 => (fillF h p g k).insert (p + k) (g k)

theorem lookup_fillF (h : Finmap (fun _ : Int => Int)) (p : Int) (g : Int → Int) :
    ∀ (k : Nat) (a : Int), (fillF h p g k).lookup a = if p ≤ a ∧ a < p + k then some (g (a - p)) else h.lookup a
  | 0, a => by simp [fillF]
  | k + 1, a => by
    rw [fillF]
    by_cases ha : a = p + k
    · subst ha; simp
    · rw [Finmap.lookup_insert_of_ne _ ha, lookup_fillF h p g k a]
      by_cases h1 : p ≤ a ∧ a < p + k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by push_cast; omega)]

/-- Cursor-3's base for n input bytes and bound OUTMAX (S-12). -/
def X0 (n om : Nat) : Int := 2080 + n + om + 1393

/-- The region's size: through the read-only area's last cell (ORDER ends at X + 152, S-14). -/
def L0 (n om : Nat) : Nat := n + om + 3473 + 153

/-- The initial contents of cell i: mode TABLE (0) with both table counters 0; n (15), OUTMAX (16), the reading flag (17),
X (2079); the input bytes at 2080; S7's tables at X+16 … X+133 and ORDER at X+134 … X+152 (S-13, S-14); every other cell 0. -/
def initCell (b : Array Nat) (om : Nat) (lit : Bool) (i : Int) : Int :=
  let n := b.size
  let X := X0 n om
  if i = 15 then n
  else if i = 16 then om
  else if i = 17 then (if lit then 1 else 0)
  else if i = 2079 then X
  else if 2080 ≤ i ∧ i < 2080 + n then b.getD (i - 2080).toNat 0
  else if X + 16 ≤ i ∧ i < X + 45 then LBASE.getD (i - X - 16).toNat 0
  else if X + 45 ≤ i ∧ i < X + 74 then LEXTRA.getD (i - X - 45).toNat 0
  else if X + 74 ≤ i ∧ i < X + 104 then DBASE.getD (i - X - 74).toNat 0
  else if X + 104 ≤ i ∧ i < X + 134 then DEXTRA.getD (i - X - 104).toNat 0
  else if X + 134 ≤ i ∧ i < X + 153 then ORDER.getD (i - X - 134).toNat 0
  else 0

/-- The initial store: ONE region of `L0` cells at base p holding `initCell` (R-a). -/
def initStore (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) : Store :=
  ⟨fillF ∅ p (initCell b om lit) (L0 b.size om), Finmap.singleton p (L0 b.size om)⟩

theorem initStore_world (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) :
    World (initStore b om lit p) p (L0 b.size om) (initCell b om lit) where
  reg := by simp [initStore]
  cell i h0 hL := by
    simp only [initStore, lookup_fillF]
    rw [if_pos (by omega)]
    simp

/-! ## The iteration -/

/-- A per-step bound on L2 steps: every mode does a bounded number of loads (R-b), and the longest (DECODE's hit, under the
dispatch) is well under it. A step that has not returned the world within it is an index fault or a stuck term. -/
def KSTEP : Nat := 512

/-- ONE step of the program from store σ: `some σ'` when the step term returns the same world capability ⟨p⟩, else `none`
(an index fault, a stuck term, or a different capability). -/
def stepS (p : Int) (σ : Store) : Option Store :=
  match run₂ KSTEP (closeAt p stepT, σ) with
  | (.ret (.const (.cap q)), σ') => if q = p then some σ' else none
  | _ => none

/-- k steps. -/
def iterS (p : Int) : Nat → Store → Option Store
  | 0, σ => some σ
  | k + 1, σ => (stepS p σ).bind (iterS p k)

def modeOf (p : Int) (σ : Store) : Int := (σ.H.lookup p).getD (-1)
def reasonOf (p : Int) (σ : Store) : Int := (σ.H.lookup (p + cREASON)).getD (-1)

/-- The output: m = cell 3 bytes at `IN + n` (S-1). -/
def outOf (p : Int) (n : Nat) (σ : Store) : Array Nat :=
  let m := ((σ.H.lookup (p + cM)).getD 0).toNat
  ((List.range m).map fun i => ((σ.H.lookup (p + (2080 + n + i))).getD 0).toNat).toArray

/-! ## The X3 (a) statements (S-5), written before their proofs -/

/-- **SAFETY.** For every OUTMAX, either reading, and every byte string b — **no premise on the bytes (D7)**: a byte string is
an array of values below 256, which is the domain, not a premise — from the initial world, no step is a fault (each step returns
the world), and the iteration reaches DONE or REJECT within a bound N that depends on n and OUTMAX alone. D3 scores the
measure that proves it. -/
def SafetyStmt : Prop :=
  ∃ N : Nat → Nat → Nat, ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int), (∀ x ∈ b, x < 256) →
    ∃ k σ', k ≤ N b.size om ∧ iterS p k (initStore b om lit p) = some σ' ∧
      (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT)

/-- **CORRECTNESS.** The iteration reaches DONE with output o iff S accepts with o, and reaches REJECT iff S rejects — for the
repaired reading (`inflate`, lit = false) and the literal one (`inflateLit`, lit = true). By simulation of Spec.lean, whose loops
are fuel-free by `*_adequate`. Reasons are compared to S8's and never scored (S-6). -/
def CorrectStmt : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int), (∀ x ∈ b, x < 256) →
    (∀ o, (∃ k σ', iterS p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mDONE ∧ outOf p b.size σ' = o) ↔
      run lit b om = .ok o) ∧
    ((∃ k σ', iterS p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mREJECT) ↔ ∃ r, run lit b om = .error r)

end VIRDeflate.Step
