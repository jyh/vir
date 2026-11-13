/-
  O95 layer L5, Lean arm (amend-24 LV7; DECLARATIONS-LEAN "The routines"): `fillR : (int × int × int) →[1] unit`, (d, len, v), writes
  v to the cells [d, d + len) of the ONE region it is lent, and hands that region back. Its triple's precondition names only the
  region, its size and the index bounds: NO premise on the contents (LV7). The proof unrolls the fix through the program logic
  (appKFix_rule₅, ite_rule₅, letOp_rule₅ with L2's `store_at`, retK_rule₅), by induction on len.
-/
import VIRL5.Ops5

namespace VIRL5
open VIRL1 VIRL2

/-- The argument type (d, (len, v)). -/
def τfill : Ty₅ := .prod t5int (.prod t5int t5int)

/-- The body, under c = #0 (the lent region), x = #1 (the argument), f = #2 (the routine itself). -/
def fillBody : Tm₅ :=
  .ite (.prim .le [.fst (.snd (.var 1)), .const (.int 0)])
    (.retK (.const .unit) [.var 0])
    (.letOp .store [.var 0, .fst (.var 1), .snd (.snd (.var 1))] t5cap
      (.appK (.var 3)
        (.pair (.prim .add [.fst (.var 2), .const (.int 1)])
          (.pair (.prim .sub [.fst (.snd (.var 2)), .const (.int 1)]) (.snd (.snd (.var 2)))))
        [.var 0]))

def fillR : Atom₅ := .fix τfill 1 t5unit fillBody

/-- What `fillR` leaves: the contents with [p + d, p + d + len) set to v. -/
def fillF (g : Int → Int) (p d : Int) (len : Nat) (v : Int) : Int → Int :=
  fun a => if p + d ≤ a ∧ a < p + d + len then v else g a

def fillArg (d : Int) (len : Nat) (v : Int) : Atom₅ := .pair (.const (.int d)) (.pair (.const (.int len)) (.const (.int v)))

theorem fillF_zero (g : Int → Int) (p d v : Int) : fillF g p d 0 v = g := by
  funext a; unfold fillF; split_ifs <;> first | rfl | omega

theorem fillF_succ (g : Int → Int) (p d v : Int) (m : Nat) :
    fillF (Function.update g (p + d) v) p (d + 1) m v = fillF g p d (m + 1) v := by
  funext a; unfold fillF
  by_cases ha : a = p + d
  · subst ha; simp
  · rw [Function.update_of_ne ha]; push_cast; split_ifs <;> first | rfl | omega

/-- The converse of a pure head step: e′ inherits e's triple when e steps to e′ (any run of e′ is a run of e after one step). -/
theorem pure_step_rev₅ {P : Assn} {e e' : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} (hstep : ∀ σ, Step₅ (e, σ) (e', σ))
    (h : Triple₅ P e Q) : Triple₅ P e' Q := by
  intro σ σf hP hd hwf
  obtain ⟨hs, hp, hk⟩ := h σ σf hP hd hwf
  exact ⟨fun c hc => hs c (.step (hstep _) hc), fun a σ' hc => hp a σ' (.step (hstep _) hc),
    fun a ds σ' hc => hk a ds σ' (.step (hstep _) hc)⟩

/-- **fillR's triple**: lent ⟨p⟩ with contents g and size n, with 0 ≤ d and d + len ≤ n, it hands ⟨p⟩ back with contents
  `fillF g p d len v`, returning unit; no premise on g. -/
theorem fillR_spec (p : Int) (n : Nat) (v : Int) : ∀ (len : Nat) (d : Int) (g : Int → Int), 0 ≤ d → d + len ≤ n →
    Triple₅ (RegionAt p n g) (.appK fillR (fillArg d len v) [.const (.cap p)])
      (fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p n (fillF g p d len v) σ)
  | 0, d, g, hd, hn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]) ?_
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p n g σ) rfl rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      exact ⟨rfl, rfl, by rw [fillF_zero]; exact hσ⟩
  | m + 1, d, g, hd, hn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]) ?_
      simp only [Bool.false_eq_true, if_false]
      refine letOp_rule₅ (cs := [.cap p, .int d, .int v]) (by simp [Atom₅.evalL, Atom₅.eval])
        (store_at p n g d v ⟨hd, by push_cast at hn; omega⟩) (fun c => ?_)
      show Triple₅ (fun σ => c = .const (.cap p) ∧ RegionAt p n (Function.update g (p + d) v) σ) _ _
      refine pre_pure₅ (fun hc => ?_)
      subst hc
      have ih := fillR_spec p n v m (d + 1) (Function.update g (p + d) v) (by omega) (by push_cast at hn ⊢; omega)
      rw [fillF_succ] at ih
      have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine appKFix_rule₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]

end VIRL5
