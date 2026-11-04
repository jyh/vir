/-
  O95 layer L3, Lean arm. R2 (G4 (a)): ⟦U⟧₂ ≠ ⟦F⟧₂, by RUNNING both terms on ONE concrete store (Z3): the world at base 0
  holding a frame with tokens and NO ACL bit. U decrements the sender's bucket before its ACL check and keeps the store at its
  refusing exit (an L2 exit keeps its stores); F refuses before any store. The only L2 facts cited are the step function's
  soundness (`run₂_steps`) and the meaning of a reached `ret` (`den₂_of_steps`).
-/
import VIRL3.Typing

namespace VIRL3
open VIRL1 VIRL2

/-- The world, an 87-cell region at base 0, with the listed cells written (every other cell 0). -/
def mkWorld (cells : List (Int × Int)) : Store :=
  cells.foldl (fun σ c => (Store.store 0 c.1 c.2 σ).getD σ)
    (((Store.alloc 87 Store.empty).map Prod.snd).getD Store.empty)

/-- Close a router term at the world ⟨0⟩ (its one free variable, #0). -/
def closeW (e : Tm₂) : Tm₂ := Tm.subst 0 (.const (.cap 0)) e

/-- The witness: LEN 24, the magic's four bytes (1297303345 = 49 · 71 · 83 · 77 little-endian), sender 0, topic 0, the ACL
  cell A + 0 left 0, and ONE token in bucket K + 0. -/
def σW : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (K, 1)]

set_option maxRecDepth 100000 in
theorem F_run : (run₂ 80 (closeW F, σW)).1 = .ret (.const (.cap 0)) := rfl
set_option maxRecDepth 100000 in
theorem U_run : (run₂ 80 (closeW U, σW)).1 = .ret (.const (.cap 0)) := rfl
set_option maxRecDepth 100000 in
theorem F_bucket : Store.load 0 K (run₂ 80 (closeW F, σW)).2 = some 1 := rfl
set_option maxRecDepth 100000 in
theorem U_bucket : Store.load 0 K (run₂ 80 (closeW U, σW)).2 = some 0 := rfl

/-- A run that reaches `ret` of a value gives the meaning (`run₂_steps` + `den₂_of_steps`). -/
theorem den_of_run {c : Config} {n : Nat} {a : Atom₂} (h : (run₂ n c).1 = .ret a) (hv : a.eval = some a) :
    den₂ c = Part.some (a, (run₂ n c).2) := by
  have hs := run₂_steps n c
  have he : run₂ n c = (.ret a, (run₂ n c).2) := by rw [← h]
  rw [he] at hs; exact den₂_of_steps hs hv

/-- R2: ⟦U⟧₂ ≠ ⟦F⟧₂ (OBJECT-L3 §3.2, G4 (a)). -/
theorem R2 : den₂ (closeW U, σW) ≠ den₂ (closeW F, σW) := by
  rw [den_of_run U_run rfl, den_of_run F_run rfl]
  intro h
  have h' := congrArg (fun p : Atom₂ × Store => Store.load 0 K p.2) (Part.some_injective h)
  simp only [U_bucket, F_bucket] at h'
  exact absurd h' (by decide)

end VIRL3
