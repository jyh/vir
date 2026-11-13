/-
  O95, K5-2 route A: the dispatch prefix (Dispatch.lean's `disp_run`/`step_dispatch`) on the checked runner. The dispatch only
  compares the mode number (`eq`, a Bool result), so it adds NO range fact: the step term is in range wherever the mode term
  it reaches is.
-/
import K5.Checked

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

theorem disp_inR (p m : Int) (σ : Store) : ∀ (ms : List (Int × NT)), (∀ kt ∈ ms, NT.ok "md" kt.2) →
    (∀ t, ms.lookup m = some t → SrcInRange (closeAt p (t.c ["w"]), σ)) →
    SrcInRange (Tm.subst 0 (VIRDeflate.Step.ci m) (Tm.subst 1 (capA p) ((dispN ms).c ["md", "w"])), σ)
  | [], _, _ => by
    simp only [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst]
    exact srcInRange_ret trivial
  | (k, t) :: r, h, hT => by
    have ht := carry_top p m t (h (k, t) (by simp))
    have heq : Tm.subst 0 (VIRDeflate.Step.ci m) (Tm.subst 1 (capA p) ((dispN ((k, t) :: r)).c ["md", "w"])) =
        Tm.ite (Atom.prim L1.Prim.eq [VIRDeflate.Step.ci m, VIRDeflate.Step.ci k]) (closeAt p (t.c ["w"]))
          (Tm.subst 0 (VIRDeflate.Step.ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))) := by
      rw [← ht]; simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL]
    rw [heq]
    by_cases hk : m = k
    · subst hk
      have hT' := hT t (by simp [List.lookup])
      refine srcInRange_step ?_ ?_ ?_
      · simp [headB, aInR, aInRL, cInR, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1]
      · simp [stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
          Const.toBool]
      · simpa [stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
          Const.toBool] using hT'
    · have hb : (m == k) = false := by simp [hk]
      have ih := disp_inR p m σ r (fun kt hkt => h kt (by simp [hkt]))
        (fun t' ht' => hT t' (by simp [List.lookup, hb, ht']))
      refine srcInRange_step ?_ ?_ ?_
      · simp [headB, aInR, aInRL, cInR, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1]
      · simp [stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
          Const.toBool, hk]
      · simpa [stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
          Const.toBool, hk] using ih

/-- **The step term is in range wherever its mode term is** (DONE, REJECT and unknown modes: a bare `ret ⟨p⟩`). -/
theorem step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) (m : Int)
    (hm : f cMODE = m) (hT : ∀ t, modes.lookup m = some t → SrcInRange (closeAt p (t.c ["w"]), σ)) :
    SrcInRange (closeAt p stepT, σ) := by
  simp only [cMODE] at hm
  have g0 := hw.get (i := 0) (by decide) (by omega) hm
  refine srcInRange_step ?_ ?_ ?_
  · simp [closeAt, stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL,
      headB, aInR, aInRL]
  · simp [closeAt, stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL,
      stepFn₂, opStep, Store.load, hw.reg, g0, Atom.eval, Atom.evalL, cMODE, hL, show (0 : Int) < L by omega]
  · have hd := disp_inR p m σ modes modes_ok hT
    have e : stepFn₂ (closeAt p stepT) σ =
        some (Tm.subst 0 (VIRDeflate.Step.ci m) (Tm.subst 1 (capA p) ((dispN modes).c ["md", "w"])), σ) := by
      simp only [closeAt, stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
        Atom.substL, stepFn₂, opStep, Store.load, hw.reg, g0, cMODE, capA]
      simp [NA.c, List.idxOf, List.findIdx, List.findIdx.go, Atom.substL, Atom.subst, Atom.eval, Atom.evalL, Store.load,
        hw.reg, hL, show (0 : Int) < L by omega, g0]
    show SrcInRange ((stepFn₂ (closeAt p stepT) σ).getD _)
    rw [e]; exact hd

end K5
