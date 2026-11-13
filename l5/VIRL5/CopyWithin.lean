/-
  O95 layer L5, Lean arm (amend-24 LV7; DECLARATIONS-LEAN "copyWithinR"): `copyWithinR : (int × int × int) →[1] unit`, (s, d, len),
  copies [s, s + len) to [d, d + len) WITHIN the one lent region, FORWARD, one cell at a time, so an overlapping copy reads cells it
  has already written (RFC 1951's back-reference: a distance shorter than the length repeats). The specification is that byte order
  (`cwF`, the loop's own recursion). Whether it collapses into copyR is LV10's to measure. NO premise on the contents (LV7).
-/
import VIRL5.Scan

namespace VIRL5
open VIRL1 VIRL2

/-- The body, under c = #0, x = (s, (d, len)) = #1, f = #2. -/
def cwBody : Tm₅ :=
  .ite (.prim .le [.snd (.snd (.var 1)), .const (.int 0)])
    (.retK (.const .unit) [.var 0])
    (.letOp .load [.var 0, .fst (.var 1)] t5int
      (.letOp .store [.var 1, .fst (.snd (.var 2)), .var 0] t5cap
        (.appK (.var 4)
          (.pair (.prim .add [.fst (.var 3), .const (.int 1)])
            (.pair (.prim .add [.fst (.snd (.var 3)), .const (.int 1)]) (.prim .sub [.snd (.snd (.var 3)), .const (.int 1)])))
          [.var 0])))

def copyWithinR : Atom₅ := .fix τcopy 1 t5unit cwBody

/-- The forward copy, cell by cell, in byte order. -/
def cwF (p : Int) : (Int → Int) → Int → Int → Nat → (Int → Int)
  | g, _, _, 0 => g
  | g, s, d, m + 1 => cwF p (Function.update g (p + d) (g (p + s))) (s + 1) (d + 1) m

/-- **copyWithinR's triple**: the region handed back with contents `cwF p g s d len`; no premise on g. -/
theorem copyWithinR_spec (p : Int) (n : Nat) : ∀ (len : Nat) (s d : Int) (g : Int → Int),
    0 ≤ s → s + len ≤ n → 0 ≤ d → d + len ≤ n →
    Triple₅ (RegionAt p n g) (.appK copyWithinR (copyArg s d len) [.const (.cap p)])
      (fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p n (cwF p g s d len) σ)
  | 0, s, d, g, hs, hsn, hd, hdn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cwBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
        (retK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p n (cwF p g s d 0) σ) rfl rfl)
  | m + 1, s, d, g, hs, hsn, hd, hdn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cwBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]
      simp only [Bool.false_eq_true, if_false]
      refine letOp_rule₅ (cs := [.cap p, .int s]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (load_at p n g s ⟨hs, by push_cast at hsn; omega⟩) (fun w => ?_)
      show Triple₅ (fun σ => w = .const (.int (g (p + s))) ∧ RegionAt p n g σ) _ _
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap p, .int d, .int (g (p + s))]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (store_at p n g d (g (p + s)) ⟨hd, by push_cast at hdn; omega⟩) (fun c => ?_)
      show Triple₅ (fun σ => c = .const (.cap p) ∧ RegionAt p n (Function.update g (p + d) (g (p + s))) σ) _ _
      refine pre_pure₅ (fun hc => ?_)
      subst hc
      have ih := copyWithinR_spec p n m (s + 1) (d + 1) (Function.update g (p + d) (g (p + s))) (by omega)
        (by push_cast at hsn ⊢; omega) (by omega) (by push_cast at hdn ⊢; omega)
      have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine appKFix_rule₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]

end VIRL5
