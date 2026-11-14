/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, SCOPY). `copyWithinR`'s contents `cwF` are the FORWARD copy in byte order,
  so an overlapping copy repeats (RFC 1951's back-reference). When the source lies wholly before the destination (s + len ≤ d,
  SCOPY's case: input [IN + by, …) before output [IN + n + m, …) because by + c ≤ n), the forward copy is the plain one:
  destination cell d + i holds source cell s + i, every other cell is unchanged. This is what turns scopy5_chunk's contents into
  DEFLATE's "the next c input bytes pushed to the output".
-/
import VIRL5.CopyWithin

namespace VIRL5
open VIRL1 VIRL2

/-- **The disjoint forward copy is the plain copy.** -/
theorem cwF_disjoint (p : Int) : ∀ (len : Nat) (g : Int → Int) (s d : Int), s + len ≤ d → ∀ a,
    cwF p g s d len a = if p + d ≤ a ∧ a < p + d + len then g (a - d + s) else g a
  | 0, g, s, d, _, a => by
    simp only [cwF]
    rw [if_neg (by push_cast; omega)]
  | m + 1, g, s, d, h, a => by
    rw [cwF, cwF_disjoint p m _ (s + 1) (d + 1) (by push_cast at h ⊢; omega) a]
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | (exfalso; push_cast at *; omega) | (congr 1; push_cast at *; omega)

end VIRL5
