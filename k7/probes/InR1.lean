import K7.World
import K5.Checked
import VIRL3.Sym
open VIRL1 VIRL2 VIRL3 VIRC K5

namespace K7

theorem srcInRange_stuck {c : Config} (hb : headB c.1 = true) (hs : stepFn₂ c.1 c.2 = none) : SrcInRange c := by
  intro S hS
  cases hS with
  | refl => exact headB_sound _ hb
  | step h _ => have := step₂_complete h; rw [hs] at this; cases this

theorem inR_sub1 {x : Int} (h0 : 0 < x) (h : inRange x = true) : inRange (x - 1) = true := by
  simp only [inRange, decide_eq_true_eq] at h ⊢; omega

set_option maxHeartbeats 4000000 in
example {σ : Store} {f : Int → Int} (hw : World σ 0 f) (hR : ∀ i, inRange (f i) = true)
    (hwire : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256) : SrcInRange (closeAt 0 F, σ) := by
  have hc : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by simpa using hw.cell i h0 h1
  have h3 := hwire 3 (by decide) (by decide)
  have h4 := hwire 4 (by decide) (by decide)
  simp only [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  refine srcInRange_step ?_ ?_ ?_ <;> simp (disch := omega) [headB, aInR, aInRL, cInR, stepFn₂, stepFn, opStep,
    Store.load, Store.store, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1,
    Const.toBool, Tm.subst, Atom.subst, Atom.substL, hw.reg, hc, inRange_eq, if_pos, if_neg]
  refine srcInRange_step ?_ ?_ ?_
  all_goals trace_state
  all_goals sorry

end K7
