/-
  L-FLAT, the control (PREDICTIONS.md: built second, scores P1b).
  Slices are an UNINDEXED structure; the bound is a separate hypothesis.
  Prediction P1b: slice_fuse needs NO index transport here (C1slice = 0).
-/
import VIR.Core

namespace VIR.Flat

structure FSlice where
  buf : ByteArray
  off : Nat
  len : Nat

def FSlice.adv (s : FSlice) (i : Nat) : FSlice := ⟨s.buf, s.off + i, s.len - i⟩

/-- `[slice_fuse]` on flat slices: an ordinary equation between values of ONE type. -/
theorem slice_fuse_flat (s : FSlice) (i j : Nat) : (s.adv i).adv j = s.adv (i + j) := by
  simp only [FSlice.adv, Nat.add_assoc, Nat.sub_sub]

end VIR.Flat
