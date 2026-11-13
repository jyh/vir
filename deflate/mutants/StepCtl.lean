/-
OBJECT-DEFLATE under X1 (a): the L2 step program (DECLARATIONS-DEFLATE.md, "The L2 step program", S-1 … S-6, declared before this
file). This file grows per row. FIRST: D4's bit-of-a-byte as an L2 term, a pure top-level `fix` over `Int` with `sub`, `lt`,
`le`, `add` and `mul` only (P unchanged), run by L2's own step function and proved equal to `bitAt` (Bits.lean) on every byte.
l1/ and l2/ are imported and never edited (D2).
-/
import VIRDeflate.Bits
import VIRL2

namespace VIRDeflate.StepCtl
open VIRL1 VIRL2

/-! ## Atoms, in de Bruijn form (these terms are small; the named layer of S-4 comes with the step itself) -/

abbrev ci (n : Int) : Atom₂ := .const (.int n)
abbrev vr (n : Nat) : Atom₂ := .var n
def padd (a b : Atom₂) : Atom₂ := .prim .add [a, b]
def psub (a b : Atom₂) : Atom₂ := .prim .sub [a, b]
def pmul (a b : Atom₂) : Atom₂ := .prim .mul [a, b]
def plt (a b : Atom₂) : Atom₂ := .prim .lt [a, b]
def ple (a b : Atom₂) : Atom₂ := .prim .le [a, b]

def tII : Ty₂ := .prod (.prod tint tint) tint
def tPow : Ty₂ := .arr tint tint
def tStrip : Ty₂ := .arr tII tint

/-- `fix pow2(k:int):int. if k ≤ 0 then 1 else 2 · pow2(k − 1)` — x = #0, pow2 = #1. -/
def POW : Atom₂ :=
  .fix tint tint <|
    .ite (ple (vr 0) (ci 0)) (.ret (ci 1)) <|
      .letE tint (.app (vr 1) (psub (vr 0) (ci 1))) (.ret (pmul (ci 2) (vr 0)))

/-- `fix strip(((n, i), v)) : int` = Bits.lean's `stripTop n i v`, with `pow2` free (de Bruijn #2 under the fix's two binders):
`if n ≤ 0 then v else let p = pow2(i + n) in let w = (if v < p then v else v − p) in strip(((n − 1, i), w))`. -/
def STRIP : Atom₂ :=
  .fix tII tint <|
    .ite (ple (.fst (.fst (vr 0))) (ci 0)) (.ret (.snd (vr 0))) <|
      -- p : #0, x : #1, strip : #2, pow2 : #3
      .letE tint (.app (vr 2) (padd (.snd (.fst (vr 0))) (.fst (.fst (vr 0))))) <|
      -- w : #0, p : #1, x : #2, strip : #3
      .letE tint (.ite (plt (.snd (vr 1)) (vr 0)) (.ret (.snd (vr 1))) (.ret (psub (.snd (vr 1)) (vr 0)))) <|
      .app (vr 3) (.pair (.pair (psub (.fst (.fst (vr 2))) (ci 1)) (.snd (.fst (vr 2)))) (vr 0))

/-- D4: `bitAt v i` as an L2 term with `v` and `i` given as constants:
`let pow2 = POW in let strip = STRIP in let r = strip(((7 − i, i), v)) in let q = pow2(i) in if r < q then 0 else 1`. -/
def bitProg (v i : Int) : Tm₂ :=
  .letE tPow (.ret POW) <|                                              -- pow2 : #0
  .letE tStrip (.ret STRIP) <|                                          -- strip : #0, pow2 : #1
  .letE tint (.app (vr 0) (.pair (.pair (ci (7 - i)) (ci i)) (ci v))) <| -- r : #0, strip : #1, pow2 : #2
  .letE tint (.app (vr 2) (ci i)) <|                                    -- q : #0, r : #1
  .ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1))

/-- The integer a terminal `ret` carries, if that is what the term is. -/
def retInt? : Tm₂ → Option Int
  | .ret (.const (.int n)) => some n
  | _ => none

theorem retInt?_eq {t : Tm₂} {n : Int} (h : retInt? t = some n) : t = .ret (ci n) := by
  unfold retInt? at h
  split at h
  · cases h; rfl
  · cases h

/-- `STRIP` with `pow2` bound, as it is once `bitProg`'s first `let` has run. -/
def STRIPc : Atom₂ := STRIP.subst 0 POW

/-! ## Running terms, compositionally (relational `Steps₂`, l2's `Steps₂.trans` / `Steps₂.letE`, and `stepFn₂_sound`)
Every call site binds a result with `let`, so each lemma is stated in that context: `let x = f(a) in e₂` steps to `e₂[v/x]`. -/

theorem steps_of {e : Tm₂} {σ : Store} {c' d : Config} (h : stepFn₂ e σ = some c') (k : Steps₂ c' d) : Steps₂ (e, σ) d :=
  .step (stepFn₂_sound h) k

/-- `let x = ret a in e₂` steps to `e₂[v/x]` when `a` evaluates to `v`. -/
theorem steps_letRet {τ : Ty₂} {a v : Atom₂} {e₂ : Tm₂} {σ : Store} (ha : Atom.eval a = some v) {d : Config}
    (k : Steps₂ (e₂.subst 0 v, σ) d) : Steps₂ (.letE τ (.ret a) e₂, σ) d :=
  steps_of (by simp [stepFn₂, ha]) k

/-- A straight-line run: `run₂ n c`, once computed, is reached. -/
theorem steps_run {c d : Config} (n : Nat) (h : run₂ n c = d) : Steps₂ c d := h ▸ run₂_steps n c

/-- The simp set that evaluates these terms. -/
macro "l2eval" : tactic => `(tactic| simp_all [STRIPc, stripTop, run₂, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, pInterp,
  L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, Tm.subst, Atom.subst, Atom.substL, POW, STRIP, ple, plt, psub,
  pmul, padd, S₂])

/-- **`pow2`**: for `a` evaluating to `k ≥ 0`, `let x = POW(a) in e₂` steps to `e₂[2^k/x]`. -/
theorem pow2_steps (k : Nat) : ∀ (a : Atom₂), Atom.eval a = some (ci k) → ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store),
    Steps₂ (.letE τ (.app POW a) e₂, σ) (e₂.subst 0 (ci (2 ^ k)), σ) := by
  induction k with
  | zero =>
    intro a ha τ e₂ σ
    exact steps_run 3 (by l2eval)
  | succ k ih =>
    intro a ha τ e₂ σ
    -- two steps: the call, then the test k+1 ≤ 0 (false)
    refine Steps₂.trans (steps_run 2 (c := (.letE τ (.app POW a) e₂, σ))
      (d := (.letE τ (.letE tint (.app POW (psub (ci ((k + 1 : Nat) : Int)) (ci 1))) (.ret (pmul (ci 2) (vr 0)))) e₂, σ))
      (by l2eval; rw [show decide ((k : Int) < 0) = false by simp]; l2eval)) ?_
    -- the recursive call, in both contexts
    refine Steps₂.trans (Steps₂.letE (ih _ (by l2eval) _ _ σ)) ?_
    -- bind 2·2^k
    refine steps_run 1 ?_
    l2eval
    ring_nf


/-- **`strip`**: for `a` evaluating to `((n, i), v)`, `let x = STRIPc(a) in e₂` steps to `e₂[stripTop n i v / x]`. -/
theorem strip_steps (n i : Nat) : ∀ (v : Int) (a : Atom₂),
    Atom.eval a = some (.pair (.pair (ci n) (ci i)) (ci v)) → ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store),
    Steps₂ (.letE τ (.app STRIPc a) e₂, σ) (e₂.subst 0 (ci (stripTop n i v)), σ) := by
  induction n with
  | zero =>
    intro v a ha τ e₂ σ
    exact steps_run 3 (by l2eval)
  | succ n ih =>
    intro v a ha τ e₂ σ
    -- the call, then the test n+1 ≤ 0 (false): we reach `let p = pow2(i + (n+1)) in …`, V the argument's value
    refine Steps₂.trans (steps_run 2 (c := (.letE τ (.app STRIPc a) e₂, σ))
      (d := (.letE τ (.letE tint (.app POW (padd (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))
                (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))))
              (.letE tint (.ite (plt (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0))
                  (.ret (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))
                  (.ret (psub (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0))))
                (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))
                  (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (vr 0))))) e₂, σ))
      (by clear ih; l2eval; all_goals (rw [show decide ((n : Int) < 0) = false by simp]; l2eval))) ?_
    -- p = 2^(i+n+1)
    refine Steps₂.trans (Steps₂.letE (pow2_steps (i + (n + 1)) _
      (by clear ih; l2eval; all_goals (push_cast; ring_nf)) _ _ σ)) ?_
    -- w, by the test v < p, then the tail call
    refine Steps₂.trans (steps_run 2
      (d := (.letE τ (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))
        (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))))
        (ci (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1)))))) e₂, σ))
      (by clear ih; by_cases hv : v < 2 ^ (i + (n + 1)) <;> l2eval <;>
        (rw [show decide (v < 2 ^ (i + (n + 1))) = false from decide_eq_false (by omega)]; l2eval))) ?_
    have hstep : stripTop (n + 1) i v = stripTop n i (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) := by
      simp only [stripTop, pow2_eq, Nat.add_assoc]
    rw [hstep]
    exact ih _ _ (by l2eval) τ e₂ σ


/-- **D4, by L2's own semantics, for every byte and bit index:** `bitProg b i` steps to `ret (bitAt b i)`. -/
theorem bitProg_steps (b i : Nat) (hi : i ≤ 7) (σ : Store) :
    Steps₂ (bitProg b i, σ) (.ret (ci (bitAt (b : Int) i)), σ) := by
  -- bind POW, then STRIPc
  refine Steps₂.trans (steps_run 2
    (d := (.letE tint (.app STRIPc (.pair (.pair (ci (7 - (i : Int))) (ci i)) (ci b)))
      (.letE tint (.app POW (ci i)) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1)))), σ))
    (by simp only [bitProg, STRIPc]; l2eval)) ?_
  -- strip
  refine Steps₂.trans (strip_steps (7 - i) i b _ (by l2eval; all_goals omega) _ _ σ) ?_
  -- pow2(i)
  refine Steps₂.trans (pow2_steps i _ (by l2eval) _ _ σ) ?_
  -- the comparison
  refine steps_run 1 ?_
  unfold bitAt
  rw [pow2_eq]
  by_cases h : stripTop (7 - i) i b < 2 ^ i
  · l2eval
  · l2eval
    all_goals (rw [show decide (stripTop (7 - i) i b < 2 ^ i) = false from decide_eq_false (by omega)]; l2eval)

/-- …hence S1's `(b >> i) & 1` (`bitAt_eq`), on every byte: **D4's L2 recursion IS S1's bit.** -/
theorem bitProg_spec (b i : Nat) (hb : b < 256) (hi : i < 8) (σ : Store) :
    Steps₂ (bitProg b i, σ) (.ret (ci (((b >>> i) &&& 1 : Nat) : Int)), σ) := by
  rw [← bitAt_eq b i hb hi]
  exact bitProg_steps b i (by omega) σ

end VIRDeflate.StepCtl
