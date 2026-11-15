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

macro "wsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp (disch := omega) [headB, aInR, aInRL,
  cInR, stepFn₂, stepFn, opStep, Store.load, Store.store, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1,
  L1.Prim.interp, Const.ofL1, Const.toBool, Tm.subst, Atom.subst, Atom.substL, inRange_eq, if_pos, if_neg, A, K, NTp, NW, NS, MAGIC, $hs,*])

macro "ws" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine srcInRange_step ?_ ?_ ?_ <;> [(wsimp [$hs,*]; done); (wsimp [$hs,*]; done); (try wsimp [$hs,*])]))

macro "wstuck" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine srcInRange_stuck ?_ ?_ <;> (wsimp [$hs,*]; done)))

set_option maxHeartbeats 4000000 in
example {σ : Store} {f : Int → Int} (hw : World σ 0 f) (hR : ∀ i, inRange (f i) = true)
    (hwire : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256) : SrcInRange (closeAt 0 F, σ) := by
  have hc : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by
    have := hw.cell i h0 h1; rwa [zero_add] at this
  have hR1 : ∀ i, 0 < f i → inRange (f i - 1) = true := fun i h => inR_sub1 h (hR i)
  have h3 := hwire 3 (by decide) (by decide); have h4 := hwire 4 (by decide) (by decide)
  have h5 := hwire 5 (by decide) (by decide); have h6 := hwire 6 (by decide) (by decide)
  have h7 := hwire 7 (by decide) (by decide); have h8 := hwire 8 (by decide) (by decide)
  have h9 := hwire 9 (by decide) (by decide); have h10 := hwire 10 (by decide) (by decide)
  have h11 := hwire 11 (by decide) (by decide); have h12 := hwire 12 (by decide) (by decide)
  have h13 := hwire 13 (by decide) (by decide); have h14 := hwire 14 (by decide) (by decide)
  have hreg := hw.reg
  simp only [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  ws [hreg, hc]
  by_cases hn : 24 ≤ f 0
  · ws [hn]
    repeat ws [hreg, hc]
    by_cases hA : 67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 +
        (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14)))) < 87
    · ws [hreg, hc, hA]
      by_cases hT : 83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) < 87
      · ws [hreg, hc, hT]
        by_cases e1 : f 3 + (256 * f 4 + (65536 * f 5 + 16777216 * f 6)) = 1297303345
        · by_cases e2 : f (67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 + (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14))))) = 1
          · by_cases e3 : 0 < f (83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))))
            · repeat ws [hreg, hc, hT, e1, e2, e3, hR1]
              exact srcInRange_ret trivial
            · repeat ws [hreg, hc, e1, e2, e3]
              exact srcInRange_ret trivial
          · repeat ws [hreg, hc, e1, e2]
            exact srcInRange_ret trivial
        · repeat ws [hreg, hc, e1]
          exact srcInRange_ret trivial
      · wstuck [hreg, hc, hT]
    · wstuck [hreg, hc, hA]
  · ws [hn]
    repeat ws [hreg, hc]
    exact srcInRange_ret trivial

end K7
