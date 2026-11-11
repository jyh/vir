/-
  O95 compiler, stage S2: SIZES (S2-R (a)) and the word offset of a variable in the flat environment.
  A capability is two words (S2-C), a function one word (a label), a sum one tag word plus the larger side, padded.
  `unit` keeps one word, so that no type has size 0 and every slice is non-empty.
-/
import VIRC.Word

namespace VIRC
open VIRL1 VIRL2

def size : Ty₂ → Nat
  | .base .cap => 2
  | .base _ => 1
  | .arr _ _ => 1
  | .prod t₁ t₂ => size t₁ + size t₂
  | .sum t₁ t₂ => 1 + max (size t₁) (size t₂)

/-- The word offset of variable n in a flat environment laid out by Γ (innermost first). -/
def offset (Γ : Ctx S₂) (n : Nat) : Nat := ((Γ.take n).map size).sum

/-- The variable's slice: its offset and its size (0 if n is out of Γ, which ⊢₂ rules out). -/
def varSlice (Γ : Ctx S₂) (n : Nat) : WOpd := .slice (offset Γ n) ((Γ[n]?.map size).getD 0)

theorem size_pos : ∀ τ, 0 < size τ
  | .base b => by cases b <;> simp [size]
  | .arr _ _ => by simp [size]
  | .prod t₁ _ => by have := size_pos t₁; simp [size]; omega
  | .sum _ _ => by simp [size]

end VIRC
