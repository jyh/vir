import VIRDeflate.Safety
import VIRDeflate.Dynamic

/-
  O95, D7's byte-type corollary (DECLARATIONS-DEFLATE, the 81st head's addendum; the non-author read's test). SAFETY and CORRECTNESS
  over `ByteArray`, with NO hypothesis on the bytes: the `∀ x ∈ b, x < 256` of `SafetyStmt`/`CorrectStmt` is discharged by
  `UInt8.toNat_lt`. Proved from `safety` and `correct` and nothing else.
-/

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-- A `ByteArray` read as the decoder's input. -/
def ofBytes (bs : ByteArray) : Array Nat := bs.data.map UInt8.toNat

theorem ofBytes_lt (bs : ByteArray) : ∀ x ∈ ofBytes bs, x < 256 := by
  intro x hx
  simp only [ofBytes, Array.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  exact UInt8.toNat_lt u

theorem ofBytes_size (bs : ByteArray) : (ofBytes bs).size = bs.size := by
  cases bs; simp only [ofBytes, Array.size_map]; rfl

/-- **SAFETY over bytes**, no premise on the input. -/
theorem safety_bytes : ∃ N : Nat → Nat → Nat, ∀ (bs : ByteArray) (om : Nat) (lit : Bool) (p : Int),
    ∃ k σ', k ≤ N bs.size om ∧ iterS p k (initStore (ofBytes bs) om lit p) = some σ' ∧
      (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT) := by
  obtain ⟨N, hN⟩ := safety
  refine ⟨N, fun bs om lit p => ?_⟩
  have := hN (ofBytes bs) om lit p (ofBytes_lt bs)
  rwa [ofBytes_size] at this

/-- **CORRECTNESS over bytes**, no premise on the input. -/
theorem correct_bytes (bs : ByteArray) (om : Nat) (lit : Bool) (p : Int) :
    (∀ o, (∃ k σ', iterS p k (initStore (ofBytes bs) om lit p) = some σ' ∧ modeOf p σ' = mDONE ∧
        outOf p (ofBytes bs).size σ' = o) ↔ run lit (ofBytes bs) om = .ok o) ∧
    ((∃ k σ', iterS p k (initStore (ofBytes bs) om lit p) = some σ' ∧ modeOf p σ' = mREJECT) ↔
        ∃ r, run lit (ofBytes bs) om = .error r) :=
  correct (ofBytes bs) om lit p (ofBytes_lt bs)

end VIRDeflate.Step
