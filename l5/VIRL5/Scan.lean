/-
  O95 layer L5, Lean arm (amend-24 LV7): `scanR : (int × int × int) →[1] int`, (from, to, v): the least i ∈ [from, to) whose cell
  holds v, else `to`; the one lent region handed back unchanged. An early exit (`retK` from inside the loop) and a result that is
  not unit. Precondition: the region, its size, the index bounds; NO premise on the contents (LV7).
-/
import VIRL5.Cmp

namespace VIRL5
open VIRL1 VIRL2

/-- The body, under c = #0, x = (from, (to, v)) = #1, f = #2. -/
def scanBody : Tm₅ :=
  .ite (.prim .le [.fst (.snd (.var 1)), .fst (.var 1)])
    (.retK (.fst (.snd (.var 1))) [.var 0])
    (.letOp .load [.var 0, .fst (.var 1)] t5int
      (.ite (.prim .eq [.var 0, .snd (.snd (.var 2))])
        (.retK (.fst (.var 2)) [.var 1])
        (.appK (.var 3) (.pair (.prim .add [.fst (.var 2), .const (.int 1)]) (.snd (.var 2))) [.var 1])))

def scanR : Atom₅ := .fix τfill 1 t5int scanBody

/-- What `scanR` returns: the first index from `from` (over len cells) whose cell holds v, else from + len. -/
def scanF (f : Int → Int) (p : Int) (v : Int) : Int → Nat → Int
  | fr, 0 => fr
  | fr, m + 1 => if f (p + fr) = v then fr else scanF f p v (fr + 1) m

def scanArg (fr tt v : Int) : Atom₅ := .pair (.const (.int fr)) (.pair (.const (.int tt)) (.const (.int v)))

/-- **scanR's triple**: the region handed back unchanged, the result `scanF f p v fr len`; no premise on f. -/
theorem scanR_spec (p : Int) (n : Nat) (f : Int → Int) (v : Int) : ∀ (len : Nat) (fr tt : Int),
    tt = fr + len → 0 ≤ fr → tt ≤ n →
    Triple₅ (RegionAt p n f) (.appK scanR (scanArg fr tt v) [.const (.cap p)])
      (fun r qs σ => r = .const (.int (scanF f p v fr len)) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
  | 0, fr, tt, hto, hfr, hn => by
      rw [show tt = fr by simpa using hto]
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, scanBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, scanArg]
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .const (.int fr) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
          (by simp [Atom₅.eval, scanArg]) rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      exact ⟨by simp [scanF], rfl, hσ⟩
  | m + 1, fr, tt, hto, hfr, hn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, scanBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, scanArg]
        omega
      simp only [Bool.false_eq_true, if_false]
      refine letOp_rule₅ (cs := [.cap p, .int fr]) (by simp [Atom₅.evalL, Atom₅.eval, scanArg])
        (load_at p n f fr ⟨hfr, by push_cast at hn hto; omega⟩) (fun w => ?_)
      show Triple₅ (fun σ => w = .const (.int (f (p + fr))) ∧ RegionAt p n f σ) _ _
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      by_cases heq : f (p + fr) = v
      · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1, Atom₅.subst, scanArg, heq]) ?_
        simp only [if_true]
        refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
          (retK_rule₅ (Q := fun r qs σ => r = .const (.int fr) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
            (by simp [Atom₅.eval, Atom₅.subst, scanArg]) rfl)
        obtain ⟨rfl, rfl, hσ⟩ := h
        exact ⟨by simp [scanF, heq], rfl, hσ⟩
      · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1, Atom₅.subst, scanArg, heq]) ?_
        simp only [Bool.false_eq_true, if_false]
        have ih := scanR_spec p n f v m (fr + 1) tt (by push_cast at hto; omega) (by omega) hn
        have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
        refine conseq₅ (fun σ h => h) (fun r qs σ h => ?_) (appKFix_rule₅ rfl ?_ rfl rfl ih')
        · obtain ⟨rfl, rfl, hσ⟩ := h
          exact ⟨by simp [scanF, heq], rfl, hσ⟩
        all_goals simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, Atom₅.subst,
          scanArg]

end VIRL5
