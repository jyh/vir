/-
  O95 layer L2, Lean arm. OBJECT-L2 §2: stores σ = (H, R), both FINITE maps (l2/DECLARATIONS-LEAN.md), and the four region
  operations as PARTIAL functions on (arguments, store): `none` is a FAULT (no step). Well-formedness is a predicate, proved
  preserved, never built into the type.
-/
import VIRL2.Sig2
import Mathlib.Data.Finmap

namespace VIRL2

/-- σ = (H, R): H the cells (address ↦ value), R the live regions (base ↦ length). -/
structure Store where
  H : Finmap (fun _ : Int => Int)
  R : Finmap (fun _ : Int => Nat)

namespace Store

/-- The empty store σ₀. -/
def empty : Store := ⟨∅, ∅⟩

/-- A cell `a` lies in the region based at `p` of length `n`. -/
def InRegion (a p : Int) (n : Nat) : Prop := p ≤ a ∧ a < p + n

/-- OBJECT-L2 §2: dom H = ⋃ regions, regions pairwise disjoint, every length positive. -/
structure WF (σ : Store) : Prop where
  pos : ∀ p n, σ.R.lookup p = some n → 0 < n
  disj : ∀ p q n m, σ.R.lookup p = some n → σ.R.lookup q = some m → p ≠ q → ∀ a, InRegion a p n → ¬ InRegion a q m
  domH : ∀ a, a ∈ σ.H ↔ ∃ p n, σ.R.lookup p = some n ∧ InRegion a p n

/-- The ends p + n of the live regions. -/
def ends (σ : Store) : Multiset Int := σ.R.entries.map fun s => s.1 + (s.2 : Int)

/-- `alloc`'s base (OBJECT-L2 §3): the least fresh base above every live region, i.e. the largest live end, or 0. -/
def nextBase (σ : Store) : Int := (ends σ).fold max 0

/-- n cells from p, every one set to v, inserted into h. -/
def fill (h : Finmap (fun _ : Int => Int)) (p : Int) (v : Int) : Nat → Finmap (fun _ : Int => Int)
  | 0 => h
  | k + 1 => (fill h p v k).insert (p + k) v

/-- n cells from p erased from h. -/
def clear (h : Finmap (fun _ : Int => Int)) (p : Int) : Nat → Finmap (fun _ : Int => Int)
  | 0 => h
  | k + 1 => (clear h p k).erase (p + k)

/-- `alloc(n)`: n > 0 fresh cells at the next base, each 0; returns the base. A non-positive n has no step. -/
def alloc (n : Int) (σ : Store) : Option (Int × Store) :=
  if 0 < n then
    let p := nextBase σ
    some (p, ⟨fill σ.H p 0 n.toNat, σ.R.insert p n.toNat⟩)
  else none

/-- `load(⟨p⟩, i)`: cell p + i when 0 ≤ i < R(p). Does NOT consume the capability (F4(a)). -/
def load (p i : Int) (σ : Store) : Option Int :=
  match σ.R.lookup p with
  | some n => if 0 ≤ i ∧ i < n then σ.H.lookup (p + i) else none
  | none => none

/-- `store(⟨p⟩, i, v)`: writes cell p + i when 0 ≤ i < R(p). -/
def store (p i v : Int) (σ : Store) : Option Store :=
  match σ.R.lookup p with
  | some n => if 0 ≤ i ∧ i < n then some ⟨σ.H.insert (p + i) v, σ.R⟩ else none
  | none => none

/-- `free(⟨p⟩)`: releases the region based at p. -/
def free (p : Int) (σ : Store) : Option Store :=
  match σ.R.lookup p with
  | some n => some ⟨clear σ.H p n, σ.R.erase p⟩
  | none => none

end Store

/-- The effect of one O₂ operation on VALUES (closed atoms): its result value and the new store, or `none` = a FAULT. -/
def opStep : Op → List Atom₂ → Store → Option (Atom₂ × Store)
  | .alloc, [.const (.int n)], σ => (Store.alloc n σ).map fun (p, σ') => (.const (.cap p), σ')
  | .load, [.const (.cap p), .const (.int i)], σ => (Store.load p i σ).map fun v => (.const (.int v), σ)
  | .store, [.const (.cap p), .const (.int i), .const (.int v)], σ =>
      (Store.store p i v σ).map fun σ' => (.const (.cap p), σ')
  | .free, [.const (.cap p)], σ => (Store.free p σ).map fun σ' => (.const .unit, σ')
  | _, _, _ => none

end VIRL2
