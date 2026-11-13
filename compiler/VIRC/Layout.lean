/-
  O95 compiler, stage S2: the LAYOUT premise (DECLARATIONS-S2, "The theorem's form") and the memory relation. `lay p` is the
  address of the region L2 bases at p. The premise: every live region fits in the address space with its 8-byte cells, regions
  are pairwise disjoint as address ranges, lengths are < 2⁶³ (so a length is a non-negative word), the store is WF, and every
  live cell holds an int in range. K6: this ONE premise serves every program. A program's layout is an instance discharged
  by its caller, never a lemma about that program.
-/
import VIRC.Lower2

namespace VIRC
open VIRL1 VIRL2

structure Layout (σ : Store) (lay : Int → W) : Prop where
  wf : σ.WF
  fits : ∀ p n, σ.R.lookup p = some n → (lay p).toNat + 8 * n ≤ 2 ^ 64 ∧ n < 2 ^ 63
  disj : ∀ p q n m, σ.R.lookup p = some n → σ.R.lookup q = some m → p ≠ q →
    (lay p).toNat + 8 * n ≤ (lay q).toNat ∨ (lay q).toNat + 8 * m ≤ (lay p).toNat
  cells : ∀ p n, σ.R.lookup p = some n → ∀ i : Nat, i < n → ∃ v, σ.H.lookup (p + i) = some v ∧ inRange v = true

/-- Every live cell's value sits at its address. -/
def MemRel (lay : Int → W) (σ : Store) (m : WMem) : Prop :=
  ∀ p n, σ.R.lookup p = some n → ∀ i : Nat, i < n → ∀ v, σ.H.lookup (p + i) = some v →
    m (cellAddr (lay p) (BitVec.ofNat 64 i)) = BitVec.ofInt 64 v

theorem cellAddr_toNat (base : W) (i : Nat) (h : base.toNat + 8 * i < 2 ^ 64) :
    (cellAddr base (BitVec.ofNat 64 i)).toNat = base.toNat + 8 * i := by
  have hi : i < 2 ^ 64 := by omega
  simp only [cellAddr, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h8 : (BitVec.toNat (8 : W)) = 8 := by decide
  rw [h8, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

/-- Two live cells share an address only if they are the same cell. -/
theorem cellAddr_inj {σ lay} (hl : Layout σ lay) {p q : Int} {n m i j : Nat}
    (hp : σ.R.lookup p = some n) (hq : σ.R.lookup q = some m) (hi : i < n) (hj : j < m)
    (h : cellAddr (lay p) (BitVec.ofNat 64 i) = cellAddr (lay q) (BitVec.ofNat 64 j)) : p = q ∧ i = j := by
  have fp := hl.fits p n hp; have fq := hl.fits q m hq
  have e := congrArg BitVec.toNat h
  rw [cellAddr_toNat _ _ (by omega), cellAddr_toNat _ _ (by omega)] at e
  by_cases hpq : p = q
  · subst hpq; rw [hp] at hq; cases hq; exact ⟨rfl, by omega⟩
  · rcases hl.disj p q n m hp hq hpq with h' | h' <;> omega

end VIRC
