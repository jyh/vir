/-
  O95 layer L5, Lean arm (DECLARATIONS-LEAN Addendum 5): each routine's COST lemma, proved with the routine and beside its triple.
  A cost is linear in the count argument, `a · len + b`, with a and b written in the statement. A client (LV8) cites these and the
  triples, never the bodies.
-/
import VIRL5.Cost5
import VIRL5.Fill

namespace VIRL5
open VIRL1 VIRL2

/-- **fillR's cost**: 3 ⟶₅ steps per cell (the call, the test, the store) and 2 to stop. -/
theorem fillR_cost (p : Int) (n : Nat) (v : Int) : ∀ (len : Nat) (d : Int) (g : Int → Int), 0 ≤ d → d + len ≤ n →
    Cost₅ (RegionAt p n g) (.appK fillR (fillArg d len v) [.const (.cap p)]) (3 * len + 2)
  | 0, d, g, hd, hn => by
      refine Cost₅.mono (n := 0 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1]) ?_
      exact cost_retK₅ _ _ _
  | m + 1, d, g, hd, hn => by
      refine Cost₅.mono (n := 3 * m + 2 + 1 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1]) ?_
      simp only [Bool.false_eq_true, if_false]
      refine cost_letOp₅ (cs := [.cap p, .int d, .int v]) (by simp [Atom₅.evalL, Atom₅.eval])
        (store_at p n g d v ⟨hd, by push_cast at hn; omega⟩) (fun c => ?_)
      show Cost₅ (fun σ => c = .const (.cap p) ∧ RegionAt p n (Function.update g (p + d) v) σ) _ _
      refine cost_pre_pure₅ (fun hc => ?_)
      subst hc
      have ih := fillR_cost p n v m (d + 1) (Function.update g (p + d) v) (by omega) (by push_cast at hn ⊢; omega)
      have ih' := cost_pure_step_rev₅ (n := 3 * m + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_appKFix₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]

end VIRL5
