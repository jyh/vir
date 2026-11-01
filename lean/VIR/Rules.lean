/-
  The 7 GIVEN rules (inputs I5): A.2's four and A.3's three, as Lean theorems over the shallow embedding.
  A rule outside these seven is an AUX rule and is named `aux_*` (harness C3).
-/
import VIR.Core

namespace VIR

/-! ### A.2 -/
theorem beta_lin {α : Type} (x : α) (e : α → Out) : letLin x e = e x := rfl

theorem dce_atom {α : Type} (a : α) (e : Out) : letAtom a (fun _ => e) = e := rfl

theorem const_fold (i j : Nat) : i + j = Nat.add i j := rfl

theorem guard_true (e₁ e₂ : Out) : guard True (fun _ => e₁) e₂ = e₁ := by
  simp [guard]

/-! ### A.3 -/

/-- The index transport at the heart of slice_fuse: the two slices have DIFFERENT TYPES
    (`Slice (n - i - j)` vs `Slice (n - (i + j))`), so they are related by `HEq`, not `=`. -/
theorem Slice.adv_adv_heq {n : Nat} (s : Slice n) (i j : Nat) (h₁ : i ≤ n) (h₂ : j ≤ n - i)
    (h₃ : i + j ≤ n) : HEq ((s.adv i h₁).adv j h₂) (s.adv (i + j) h₃) := by
  have e : n - i - j = n - (i + j) := by omega
  unfold Slice.adv
  simp only [Nat.add_assoc]
  rw [e]

/-- `[slice_fuse]` with a length-polymorphic continuation (the A.3 `e[s₂]`). -/
theorem slice_fuse {n : Nat} (b : Slice n) (i j : Nat) (h₁ : i ≤ n) (h₂ : j ≤ n - i) (h₃ : i + j ≤ n)
    (e : (m : Nat) → Slice m → Out) :
    advance b i h₁ (fun s₁ => advance s₁ j h₂ (fun s₂ => e _ s₂)) = advance b (i + j) h₃ (fun s₂ => e _ s₂) := by
  have e' : n - i - j = n - (i + j) := by omega
  have hs := Slice.adv_adv_heq b i j h₁ h₂ h₃
  unfold advance
  revert hs
  generalize (b.adv i h₁).adv j h₂ = x
  generalize b.adv (i + j) h₃ = y
  revert x
  rw [e']
  intro x hs
  cases hs
  rfl

/-- `[guard_merge]`, as written: both guards share `e_err`, and `e_ok` does not use the guards' proofs. -/
theorem guard_merge (c₁ c₂ : Prop) [Decidable c₁] [Decidable c₂] (ok err : Out) :
    guard c₁ (fun _ => guard c₂ (fun _ => ok) err) err = guard (c₁ ∧ c₂) (fun _ => ok) err := by
  unfold guard; by_cases h₁ : c₁ <;> by_cases h₂ : c₂ <;> simp [h₁, h₂]

/-- `[read_comm]`: a read commutes with a linear state update it does not depend on. -/
theorem read_comm {n : Nat} {σ : Type} (b : Slice n) (i j : Nat) (upd : UInt32 → σ)
    (e : UInt32 → σ → UInt32 → Out) :
    readU32 b i (fun v₁ => letLin (upd v₁) (fun st' => readU32 b j (fun v₂ => e v₁ st' v₂)))
      = readU32 b i (fun v₁ => readU32 b j (fun v₂ => letLin (upd v₁) (fun st' => e v₁ st' v₂))) := rfl

end VIR
