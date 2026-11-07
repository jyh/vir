/-
  O95 layer L3, Lean arm. Symbolic runs over an ARBITRARY store holding the world (for R3, R4): the world is a live 87-cell
  region at base p whose cell i holds f i. A run is computed by `simp` through `run₂`, `stepFn₂`, `opStep` and the store
  operations, with the world's lookups as rewrite rules; the step function's soundness turns it into a meaning.
-/
import VIRL3.R3False

namespace VIRL3
open VIRL1 VIRL2

/-- The world at base p in σ, its contents f. -/
structure World (σ : Store) (p : Int) (f : Int → Int) : Prop where
  reg : σ.R.lookup p = some 87
  cell : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup (p + i) = some (f i)

/-- Close a router term at the world ⟨p⟩. -/
def closeAt (p : Int) (e : Tm₂) : Tm₂ := Tm.subst 0 (.const (.cap p)) e

theorem den_of_run' {c : Config} {n : Nat} {a : Atom₂} {σ' : Store} (h : run₂ n c = (.ret a, σ'))
    (hv : a.eval = some a) : den₂ c = Part.some (a, σ') := by
  have hs := run₂_steps n c
  rw [h] at hs; exact den₂_of_steps hs hv

/-- Test: a short frame (LEN < 24) makes F exit with code 1. -/
theorem F_short {σ p f} (hw : World σ p f) (hn : f 0 < 24) :
    run₂ 80 (closeAt p F, σ) = (.ret (.const (.cap p)), ⟨σ.H.insert (p + 1) 1, σ.R⟩) := by
  have h0 := hw.cell 0 (by decide) (by decide)
  have h1 : (1 : Int) < 87 := by decide
  simp [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, hw.cell, opStep, Store.load, Store.store,
    hw.reg, h0, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, Const.toBool,
    show ¬ (24 ≤ f 0) from by omega]

end VIRL3

namespace VIRL3
open VIRL1 VIRL2

/-- The sender and topic the frame carries (little-endian, the shape `RD32`'s sum takes). -/
def Sv (f : Int → Int) : Int := f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))
def Tv (f : Int → Int) : Int := f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14))

theorem insert_self_of_lookup {H : Finmap (fun _ : Int => Int)} {k v : Int} (h : H.lookup k = some v) :
    H.insert k v = H := by
  apply Finmap.ext_lookup; intro x
  by_cases hx : x = k
  · subst hx; rw [Finmap.lookup_insert, h]
  · rw [Finmap.lookup_insert_of_ne _ hx]

/-- The simp set of a symbolic run. -/
macro "symrun" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [closeAt, F, U_tx, Utxn, Ugen, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub,
    mul, le, lt, eq, conj, List.map, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂,
    stepFn₂, stepFn, opStep, Store.load, Store.store, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1,
    L1.Prim.interp, Const.ofL1, Const.toBool, A, K, NW, NS, NTp, MAGIC, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    $hs,*])

end VIRL3
