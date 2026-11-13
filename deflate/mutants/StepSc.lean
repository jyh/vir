/-
OBJECT-DEFLATE under X1 (a): the L2 step program (DECLARATIONS-DEFLATE.md, "The L2 step program", S-1 … S-6, declared before this
file). This file grows per row. FIRST: D4's bit-of-a-byte as an L2 term, a pure top-level `fix` over `Int` with `sub`, `lt`,
`le`, `add` and `mul` only (P unchanged), run by L2's own step function and proved equal to `bitAt` (Bits.lean) on every byte.
l1/ and l2/ are imported and never edited (D2).
-/
import VIRDeflate.Bits
import VIRL2

namespace VIRDeflate.StepSc
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


/-! ## D4's terms are well-typed L2: `bitProg` at ⊢₂, closed, with Δ = ∅, and both `fix` bodies checked with Δ = ∅ (the rule) -/

theorem mask_empty_replicate (k : Nat) : Mask.empty (List.replicate k false) := by
  intro n h
  rw [List.getElem?_replicate] at h
  split at h <;> simp at h

theorem fix_typed {Γ : Ctx S₂} {τ₁ τ₂ : Ty₂} {e : Tm₂} (h1 : hasCap τ₁ = false) (h2 : hasCap τ₂ = false)
    (h : HasType₂ (τ₁ :: .arr τ₁ τ₂ :: Γ) (List.replicate (Γ.length + 2) false) e τ₂) :
    HasTypeA₂ Γ (.fix τ₁ τ₂ e) (.arr τ₁ τ₂) :=
  HasTypeA₂.fix h1 h2 (mask_empty_replicate _) (by simp) h

macro "l2type" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none
  | exact mask_empty_replicate _
  | exact (mask_empty_replicate 0 : Mask.empty [])
  | (intro n; rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [tint, tcap])
  | (right; rfl)
  | rfl
  | apply HasType₂.ret | apply HasType₂.letE | apply HasType₂.app | apply HasType₂.ite
  | apply HasTypeA₂.var | apply HasTypeA₂.int | apply HasTypeA₂.prim
  | apply HasTypeA₂.pair | apply HasTypeA₂.fst | apply HasTypeA₂.snd
  | apply fix_typed rfl rfl
  | apply HasTypeL₂.cons | apply HasTypeL₂.nil))

theorem POW_typed : HasTypeA₂ [] POW tPow := by
  refine HasTypeA₂.fix (Δ := List.replicate 2 false) rfl rfl (mask_empty_replicate _) rfl ?_
  unfold ple psub pmul
  l2type

theorem STRIP_typed : HasTypeA₂ [tPow] STRIP tStrip := by
  refine HasTypeA₂.fix (Δ := List.replicate 3 false) rfl rfl (mask_empty_replicate _) rfl ?_
  unfold ple plt padd psub
  l2type

/-- **D4's program is a closed, well-typed L2 term, with no capability anywhere.** -/
theorem bitProg_typed (v i : Int) : HasType₂ [] [] (bitProg v i) tint := by
  unfold bitProg plt
  refine HasType₂.letE Split.nil (Or.inr rfl) (HasType₂.ret (mask_empty_replicate 0) POW_typed) ?_
  refine HasType₂.letE (Split.none Split.nil) (Or.inr rfl)
    (HasType₂.ret (mask_empty_replicate 1) STRIP_typed) ?_
  l2type


/-! ## `BITc`: the bit of a byte as ONE closed `fix` atom, the form the step program calls -/

/-- `fix bit((v, i)) : int. let r = STRIPc(((7 − i, i), v)) in let q = POW(i) in if r < q then 0 else 1` (x = #0, bit = #1). -/
def BITc : Atom₂ :=
  .fix (.prod tint tint) tint <|
    .letE tint (.app STRIPc (.pair (.pair (psub (ci 7) (.snd (vr 0))) (.snd (vr 0))) (.fst (vr 0)))) <|   -- r : #0, x : #1
    .letE tint (.app POW (.snd (vr 1))) <|                                                                -- q : #0, r : #1
    .ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1))

/-- **The step's bit call:** for `a` evaluating to `(b, i)` with `i ≤ 7`, `let x = BITc(a) in e₂` steps to `e₂[bitAt b i / x]`. -/
theorem bit_steps (b : Int) (i : Nat) (hi : i ≤ 7) (a : Atom₂) (ha : Atom.eval a = some (.pair (ci b) (ci i)))
    (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    Steps₂ (.letE τ (.app BITc a) e₂, σ) (e₂.subst 0 (ci (bitAt b i)), σ) := by
  -- the call
  refine Steps₂.trans (steps_run 1
    (d := (.letE τ (.letE tint (.app STRIPc (.pair (.pair (psub (ci 7) (.snd (.pair (ci b) (ci i))))
        (.snd (.pair (ci b) (ci i)))) (.fst (.pair (ci b) (ci i)))))
      (.letE tint (.app POW (.snd (.pair (ci b) (ci i)))) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1))))) e₂, σ))
    (by simp only [BITc]; l2eval)) ?_
  -- strip
  refine Steps₂.trans (Steps₂.letE (strip_steps (7 - i) i b _
    (by rw [show ((7 - i : Nat) : Int) = 7 - (i : Int) by omega]; l2eval) _ _ σ)) ?_
  -- pow2(i)
  refine Steps₂.trans (Steps₂.letE (pow2_steps i _ (by l2eval) _ _ σ)) ?_
  -- the comparison, then the binding
  refine steps_run 2 ?_
  unfold bitAt
  rw [pow2_eq]
  by_cases h : stripTop (7 - i) i b < 2 ^ i
  · rw [if_pos h]; l2eval
  · rw [if_neg h]; l2eval
    all_goals (rw [show decide (stripTop (7 - i) i b < 2 ^ i) = false from decide_eq_false (by omega)]; l2eval)

theorem BITc_typed : HasTypeA₂ [] BITc (.arr (.prod tint tint) tint) := by
  simp only [BITc, STRIPc, STRIP, POW, Atom.subst, Tm.subst, Atom.substL, ple, plt, psub, pmul, padd]
  l2type


/-! ## The world (S-1): ONE region of `L` cells at base `p`, its contents a function `f` (L3's `World`, with `L` a parameter) -/

structure World (σ : Store) (p : Int) (L : Nat) (f : Int → Int) : Prop where
  reg : σ.R.lookup p = some L
  cell : ∀ i : Int, 0 ≤ i → i < L → σ.H.lookup (p + i) = some (f i)

/-- A `store` inside the region keeps it a world, with the contents updated at that cell. -/
theorem World.store {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) {i v : Int} (_hi0 : 0 ≤ i)
    (_hiL : i < L) : World ⟨σ.H.insert (p + i) v, σ.R⟩ p L (Function.update f i v) where
  reg := hw.reg
  cell j hj0 hjL := by
    by_cases hj : j = i
    · subst hj; simp
    · rw [Finmap.lookup_insert_of_ne _ (by omega), Function.update_of_ne hj]
      exact hw.cell j hj0 hjL

/-- Close a step term at the world's capability ⟨p⟩ (the step has `world` as de Bruijn #0). -/
def closeAt (p : Int) (e : Tm₂) : Tm₂ := Tm.subst 0 (.const (.cap p)) e

/-! ## The named layer (S-4): L3's `NT.c` idea, with `fix` atoms, `app`, pairs and projections -/

inductive NA where
  | v (x : String)
  | i (n : Int)
  | p2 (o : L1.Prim) (a b : NA)
  | p1 (o : L1.Prim) (a : NA)
  | pair (a b : NA)
  | fst (a : NA)
  | snd (a : NA)
  | atom (a : Atom₂)            -- a CLOSED atom, e.g. `BITc`

inductive NT where
  | ret (a : NA)
  | letE (x : String) (τ : Ty₂) (e₁ e₂ : NT)
  | op (x : String) (τ : Ty₂) (o : Op) (as : List NA) (e : NT)
  | ite (a : NA) (e₁ e₂ : NT)
  | app (f a : NA)

/-- Compile a named atom in scope Γ (innermost first). -/
def NA.c (Γ : List String) : NA → Atom₂
  | .v x => .var (Γ.idxOf x)
  | .i n => .const (.int n)
  | .p2 o a b => .prim o [a.c Γ, b.c Γ]
  | .p1 o a => .prim o [a.c Γ]
  | .pair a b => .pair (a.c Γ) (b.c Γ)
  | .fst a => .fst (a.c Γ)
  | .snd a => .snd (a.c Γ)
  | .atom a => a

def NT.c (Γ : List String) : NT → Tm₂
  | .ret a => .ret (a.c Γ)
  | .letE x τ e₁ e₂ => .letE τ (e₁.c Γ) (e₂.c (x :: Γ))
  | .op x τ o as e => .letOp o (as.map (NA.c Γ)) τ (e.c (x :: Γ))
  | .ite a e₁ e₂ => .ite (a.c Γ) (e₁.c Γ) (e₂.c Γ)
  | .app f a => .app (f.c Γ) (a.c Γ)

/-! ## Smoke: one load through the named layer, run by `simp` on a symbolic world -/

def smokeN : NT := .op "x" tint .load [.v "w", .i 3] (.ret (.v "w"))

theorem smoke_run {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 3 < L) :
    run₂ 2 (closeAt p (smokeN.c ["w"]), σ) = (.ret (.const (.cap p)), σ) := by
  have h3 := hw.cell (3 : Int) (by norm_num) (by omega)
  simp [closeAt, smokeN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂,
    stepFn₂, stepFn, opStep, Store.load, hw.reg, h3, Atom.eval, Atom.evalL, show (3 : Int) < L by omega]


/-! ## The layout (S-1, S-7): cursor cells, then the bit table at `BT` -/

def cMODE : Int := 0
def cTB : Int := 18      -- the table's byte counter
def cTI : Int := 19      -- the table's bit counter
def BT : Int := 20       -- the bit table: cell BT + 8·b + i = bit i of byte b
def mTABLE : Int := 0
def mHDR : Int := 1

/-- `TABLE` (S-7): one cell of the bit table per step, by one call of D4's `BITc`; at 256 bytes, move to `HDR`. -/
def tableN : NT :=
  .op "tb" tint .load [.v "w", .i cTB] <|
  .op "ti" tint .load [.v "w", .i cTI] <|
  .letE "x" tint (.app (.atom BITc) (.pair (.v "tb") (.v "ti"))) <|
  .op "w1" tcap .store [.v "w", .p2 .add (.i BT) (.p2 .add (.p2 .mul (.i 8) (.v "tb")) (.v "ti")), .v "x"] <|
  .letE "nb" (.prod tint tint)
    (.ite (.p2 .eq (.v "ti") (.i 7)) (.ret (.pair (.p2 .add (.v "tb") (.i 1)) (.i 0)))
      (.ret (.pair (.v "tb") (.p2 .add (.v "ti") (.i 1))))) <|
  .op "w2" tcap .store [.v "w1", .i cTB, .fst (.v "nb")] <|
  .op "w3" tcap .store [.v "w2", .i cTI, .snd (.v "nb")] <|
  .ite (.p2 .eq (.fst (.v "nb")) (.i 256))
    (.op "w4" tcap .store [.v "w3", .i cMODE, .i mHDR] (.ret (.v "w4")))
    (.ret (.v "w3"))

def tableT : Tm₂ := tableN.c ["w"]

/-- `BITc` is closed: no substitution touches it. -/
theorem BITc_subst (k : Nat) (v : Atom₂) : BITc.subst k v = BITc := by
  simp [BITc, STRIPc, STRIP, POW, Atom.subst, Tm.subst, Atom.substL, ple, plt, psub, pmul, padd]

/-- Run k computed steps to a `BITc` call, take the call by `bit_steps`, and continue: the continuation `K` is never written out,
it is whatever the computed run reaches. -/
theorem steps_via_bit {c : Config} (k : Nat) {b : Int} {i : Nat} (hi : i ≤ 7) {K : Tm₂} {σ₁ : Store} {d : Config}
    (h1 : run₂ k c = (.letE tint (.app BITc (.pair (ci b) (ci i))) K, σ₁))
    (h2 : Steps₂ (K.subst 0 (ci (bitAt b i)), σ₁) d) : Steps₂ c d :=
  Steps₂.trans (steps_run k h1) (Steps₂.trans (bit_steps b i hi _ (by simp [Atom.eval]) tint K σ₁) h2)

/-- The counters after `TABLE`'s step: (tb, ti + 1), or (tb + 1, 0) after bit 7. -/
def tblNext (tb ti : Int) : Int × Int := if ti = 7 then (tb + 1, 0) else (tb, ti + 1)

/-- The cells `TABLE`'s step writes: the table cell, then the two counters. -/
def tblH (H : Finmap (fun _ : Int => Int)) (p tb ti : Int) : Finmap (fun _ : Int => Int) :=
  ((H.insert (p + (20 + (8 * tb + ti))) (bitAt tb ti.toNat)).insert (p + 18) (tblNext tb ti).1).insert (p + 19)
    (tblNext tb ti).2

/-- **`TABLE`, one step:** from a world with the counters (tb, ti), tb < 256, ti ≤ 7, the step writes bit ti of byte tb at
`BT + 8·tb + ti`, advances the counters with a carry, moves to `HDR` when tb reaches 256, and gives the world back. -/
theorem table_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2068 ≤ L)
    (tb ti : Nat) (htb : f cTB = tb) (hti : f cTI = ti) (htb8 : tb < 256) (hti8 : ti ≤ 7) :
    Steps₂ (closeAt p tableT, σ)
      (.ret (.const (.cap p)),
        if (tblNext tb ti).1 = 256 then ⟨(tblH σ.H p tb ti).insert (p + 0) 1, σ.R⟩ else ⟨tblH σ.H p tb ti, σ.R⟩) := by
  have hb := hw.cell 18 (by decide) (by omega)
  have hi := hw.cell 19 (by decide) (by omega)
  simp only [cTB, cTI] at htb hti
  apply steps_via_bit 2 (b := (tb : Int)) hti8
  · conv_lhs => simp [closeAt, tableT, tableN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst,
      Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, hw.reg, hb, hi, htb, hti, Atom.eval, Atom.evalL,
      cTB, cTI, BITc_subst, show (18 : Int) < L by omega, show (19 : Int) < L by omega]
  · refine steps_run 10 ?_
    by_cases h7 : ti = 7
    · subst h7
      have hidx : (20 : Int) + (8 * tb + 7) < L := by omega
      have hnn : (0 : Int) ≤ 20 + (8 * tb + 7) := by omega
      by_cases h256 : tb + 1 = 256
      · have h256' : (tb : Int) + 1 = 256 := by exact_mod_cast h256
        simp [tblH, tblNext, h256', hidx, hnn, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.store,
          hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, BT,
          cMODE, mHDR, show (18 : Int) < L by omega, show (19 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
      · have h256' : ¬ ((tb : Int) + 1 = 256) := by exact_mod_cast h256
        simp [tblH, tblNext, h256', hidx, hnn, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.store,
          hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, BT,
          cMODE, mHDR, show (18 : Int) < L by omega, show (19 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
    · have h7' : ¬ ((ti : Int) = 7) := by exact_mod_cast h7
      have hidx : (20 : Int) + (8 * tb + ti) < L := by omega
      have hnn : (0 : Int) ≤ 20 + (8 * tb + ti) := by omega
      have htb' : ¬ ((tb : Int) = 256) := by omega
      simp [tblH, tblNext, h7', htb', hidx, hnn, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.store,
          hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, BT,
          cMODE, mHDR, show (18 : Int) < L by omega, show (19 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-! ## `READ` (S-8): ONE bit per step, LSB-first into `acc`; truncation decided here and nowhere else -/

def cBY : Int := 1       -- the input byte index
def cBI : Int := 2       -- the bit index in that byte
def cREASON : Int := 14
def cN : Int := 15
def cK : Int := 2068     -- cursor-2: bits left in the field
def cACC : Int := 2069
def cWT : Int := 2070
def cRET : Int := 2071
def IN : Int := 2080     -- the input, n cells
def mREAD : Int := 2
def mREJECT : Int := 99
def rTRUNC : Int := 1

def readN : NT :=
  .op "by" tint .load [.v "w", .i cBY] <|
  .op "bi" tint .load [.v "w", .i cBI] <|
  .op "n" tint .load [.v "w", .i cN] <|
  .ite (.p2 .lt (.v "by") (.v "n"))
    (.op "v" tint .load [.v "w", .p2 .add (.i IN) (.v "by")] <|
     .op "x" tint .load [.v "w", .p2 .add (.i BT) (.p2 .add (.p2 .mul (.i 8) (.v "v")) (.v "bi"))] <|
     .op "k" tint .load [.v "w", .i cK] <|
     .op "acc" tint .load [.v "w", .i cACC] <|
     .op "wt" tint .load [.v "w", .i cWT] <|
     .op "rt" tint .load [.v "w", .i cRET] <|
     .letE "nb" (.prod tint tint)
       (.ite (.p2 .eq (.v "bi") (.i 7)) (.ret (.pair (.p2 .add (.v "by") (.i 1)) (.i 0)))
         (.ret (.pair (.v "by") (.p2 .add (.v "bi") (.i 1))))) <|
     .op "w1" tcap .store [.v "w", .i cBY, .fst (.v "nb")] <|
     .op "w2" tcap .store [.v "w1", .i cBI, .snd (.v "nb")] <|
     .op "w3" tcap .store [.v "w2", .i cACC, .p2 .add (.v "acc") (.p2 .mul (.v "x") (.v "wt"))] <|
     .op "w4" tcap .store [.v "w3", .i cWT, .p2 .mul (.i 2) (.v "wt")] <|
     .op "w5" tcap .store [.v "w4", .i cK, .p2 .sub (.v "k") (.i 1)] <|
     .ite (.p2 .eq (.p2 .sub (.v "k") (.i 1)) (.i 0))
       (.op "w6" tcap .store [.v "w5", .i cMODE, .v "rt"] (.ret (.v "w6")))
       (.ret (.v "w5")))
    (.op "w1" tcap .store [.v "w", .i cREASON, .i rTRUNC] <|
     .op "w2" tcap .store [.v "w1", .i cMODE, .i mREJECT] (.ret (.v "w2")))

def readT : Tm₂ := readN.c ["w"]

/-- The cells `READ`'s step writes when a bit remains: the cursor (with a carry), acc, wt, k. -/
def rdH (H : Finmap (fun _ : Int => Int)) (p bx bi acc wt k t : Int) : Finmap (fun _ : Int => Int) :=
  ((((H.insert (p + 1) (tblNext bx bi).1).insert (p + 2) (tblNext bx bi).2).insert (p + 2069) (acc + t * wt)).insert
    (p + 2070) (2 * wt)).insert (p + 2068) (k - 1)

set_option maxHeartbeats 1000000 in
/-- **`READ`, one step, a bit remaining (`readbit_step`):** from a world whose cursor is (bx, bi), bx < n, whose input cell
`by` holds the byte v < 256 and whose table cell `8·v + bi` holds t, the step adds t·wt to acc, doubles wt, counts k down,
advances the cursor with a carry, returns to `rt` when k reaches 0, and gives the world back. -/
theorem readbit_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (bx bi n v : Nat) (k acc wt rt t : Int) (hL : 2080 + n ≤ L)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hbyn : bx < n) (hbi7 : bi ≤ 7)
    (hv : f (IN + bx) = v) (hv8 : v < 256) (ht : f (BT + (8 * v + bi)) = t)
    (hk : f cK = k) (hacc : f cACC = acc) (hwt : f cWT = wt) (hrt : f cRET = rt) :
    Steps₂ (closeAt p readT, σ)
      (.ret (.const (.cap p)),
        if k - 1 = 0 then ⟨(rdH σ.H p bx bi acc wt k t).insert (p + 0) rt, σ.R⟩ else ⟨rdH σ.H p bx bi acc wt k t, σ.R⟩) := by
  simp only [cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET] at hby hbi hn hv ht hk hacc hwt hrt
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have hiv := hw.cell (2080 + bx) (by omega) (by omega)
  have hit := hw.cell (20 + (8 * v + bi)) (by omega) (by omega)
  have hik := hw.cell 2068 (by decide) (by omega)
  have hia := hw.cell 2069 (by decide) (by omega)
  have hiw := hw.cell 2070 (by decide) (by omega)
  have hir := hw.cell 2071 (by decide) (by omega)
  rw [hby] at h1; rw [hbi] at h2; rw [hn] at h15; rw [hv] at hiv; rw [ht] at hit
  rw [hk] at hik; rw [hacc] at hia; rw [hwt] at hiw; rw [hrt] at hir
  have hlt : (bx : Int) < n := by exact_mod_cast hbyn
  have hiL : (2080 : Int) + bx < L := by omega
  have hi0 : (0 : Int) ≤ 2080 + bx := by omega
  have htL : (20 : Int) + (8 * v + bi) < L := by omega
  have ht0 : (0 : Int) ≤ 20 + (8 * v + bi) := by omega
  have hL1 : (1 : Int) < L := by omega
  have hL2 : (2 : Int) < L := by omega
  have hL15 : (15 : Int) < L := by omega
  have hL0 : (0 : Int) < L := by omega
  have hL0' : 0 < L := by omega
  have hLk : (2068 : Int) < L := by omega
  have hLa : (2069 : Int) < L := by omega
  have hLw : (2070 : Int) < L := by omega
  have hLr : (2071 : Int) < L := by omega
  refine steps_run 40 ?_
  by_cases h7 : bi = 7
  · subst h7
    simp only [Nat.cast_ofNat] at hit htL ht0 h2
    by_cases hk1 : k - 1 = 0 <;>
    simp [closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, rdH, tblNext, hk1, hlt,
      Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15, hiv,
      hit, hik, hia, hiw, hir, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
      Const.toBool, cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET, cMODE, cREASON,
      hiL, hi0, htL, ht0, hL1, hL2, hL15, hL0, hL0', hLk, hLa, hLw, hLr]
  · have h7' : ¬ ((bi : Int) = 7) := by exact_mod_cast h7
    by_cases hk1 : k - 1 = 0 <;>
    simp [closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, rdH, tblNext, h7', hk1, hlt,
      Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15, hiv,
      hit, hik, hia, hiw, hir, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1,
      Const.toBool, cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET, cMODE, cREASON,
      hiL, hi0, htL, ht0, hL1, hL2, hL15, hL0, hL0', hLk, hLa, hLw, hLr]

/-- **`READ`, one step, no bit remaining (`readbit_trunc`):** bx ≥ n sets reason "truncated" and mode REJECT, and nothing else. -/
theorem readbit_trunc {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bx n : Int) (hby : f cBY = bx) (hn : f cN = n) (hbyn : n ≤ bx) :
    Steps₂ (closeAt p readT, σ)
      (.ret (.const (.cap p)), ⟨(σ.H.insert (p + 14) 1).insert (p + 0) 99, σ.R⟩) := by
  simp only [cBY, cN] at hby hn
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  rw [hby] at h1; rw [hn] at h15
  have hnlt : ¬ (bx < n) := by omega
  refine steps_run 10 ?_
  simp [closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, hnlt,
    Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15,
    Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool,
    cBY, cBI, cN, cMODE, cREASON, rTRUNC, mREJECT,
    show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
    show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-! ## `HDR`, `HDRB`, `HDRD` (S-8): the block header as two `READ` fields, then the dispatch on BTYPE -/

def cBF : Int := 4
def cFILL : Int := 10
def mHDRB : Int := 3
def mHDRD : Int := 4
def mSHDR : Int := 5
def mFIXLENS : Int := 6
def mDHDR : Int := 7
def rBTYPE : Int := 2

/-- Request a `READ` field of `k` bits returning to mode `rt`, then give the world back (from capability `w0`). -/
def reqN (w0 : String) (k rt : Int) : NT :=
  .op "q1" tcap .store [.v w0, .i cK, .i k] <|
  .op "q2" tcap .store [.v "q1", .i cACC, .i 0] <|
  .op "q3" tcap .store [.v "q2", .i cWT, .i 1] <|
  .op "q4" tcap .store [.v "q3", .i cRET, .i rt] <|
  .op "q5" tcap .store [.v "q4", .i cMODE, .i mREAD] (.ret (.v "q5"))

/-- `HDR`: request BFINAL (1 bit), returning to `HDRB`. -/
def hdrN : NT := reqN "w" 1 mHDRB
/-- `HDRB`: BFINAL is in acc; keep it, then request BTYPE (2 bits), returning to `HDRD`. -/
def hdrbN : NT :=
  .op "a" tint .load [.v "w", .i cACC] <|
  .op "w1" tcap .store [.v "w", .i cBF, .v "a"] (reqN "w1" 2 mHDRD)
/-- `HDRD`: BTYPE is in acc: 0 → SHDR, 1 → FIXLENS (fill index 0), 2 → DHDR, otherwise "invalid block type", REJECT. -/
def hdrdN : NT :=
  .op "a" tint .load [.v "w", .i cACC] <|
  .ite (.p2 .eq (.v "a") (.i 0)) (.op "w1" tcap .store [.v "w", .i cMODE, .i mSHDR] (.ret (.v "w1"))) <|
  .ite (.p2 .eq (.v "a") (.i 1))
    (.op "w1" tcap .store [.v "w", .i cFILL, .i 0] (.op "w2" tcap .store [.v "w1", .i cMODE, .i mFIXLENS] (.ret (.v "w2")))) <|
  .ite (.p2 .eq (.v "a") (.i 2)) (.op "w1" tcap .store [.v "w", .i cMODE, .i mDHDR] (.ret (.v "w1"))) <|
  .op "w1" tcap .store [.v "w", .i cREASON, .i rBTYPE] (.op "w2" tcap .store [.v "w1", .i cMODE, .i mREJECT] (.ret (.v "w2")))

def hdrT : Tm₂ := hdrN.c ["w"]
def hdrbT : Tm₂ := hdrbN.c ["w"]
def hdrdT : Tm₂ := hdrdN.c ["w"]

/-- The cells a field request writes: k, acc = 0, wt = 1, ret, mode = READ. -/
def reqH (H : Finmap (fun _ : Int => Int)) (p k rt : Int) : Finmap (fun _ : Int => Int) :=
  ((((H.insert (p + 2068) k).insert (p + 2069) 0).insert (p + 2070) 1).insert (p + 2071) rt).insert (p + 0) 2

/-- **`HDR`, one step:** it requests one bit returning to `HDRB`. -/
theorem hdr_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L) :
    Steps₂ (closeAt p hdrT, σ) (.ret (.const (.cap p)), ⟨reqH σ.H p 1 3, σ.R⟩) := by
  refine steps_run 10 ?_
  simp [closeAt, hdrT, hdrN, reqN, reqH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
    Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.store, hw.reg, Atom.eval, Atom.evalL, cK, cACC, cWT, cRET, cMODE,
    mREAD, mHDRB, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega,
    show (2071 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-- **`HDRB`, one step:** BFINAL (acc) is kept in its cell, and two bits are requested returning to `HDRD`. -/
theorem hdrb_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    Steps₂ (closeAt p hdrbT, σ) (.ret (.const (.cap p)), ⟨reqH (σ.H.insert (p + 4) a) p 2 4, σ.R⟩) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  refine steps_run 10 ?_
  simp [closeAt, hdrbT, hdrbN, reqN, reqH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
    Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, cK, cACC, cWT,
    cRET, cMODE, cBF, mREAD, mHDRD, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega,
    show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (4 : Int) < L by omega,
    show (0 : Int) < L by omega, show 0 < L by omega]

/-- The cells `HDRD` writes, by BTYPE. -/
def hdrdH (H : Finmap (fun _ : Int => Int)) (p a : Int) : Finmap (fun _ : Int => Int) :=
  if a = 0 then H.insert (p + 0) 5
  else if a = 1 then (H.insert (p + 10) 0).insert (p + 0) 6
  else if a = 2 then H.insert (p + 0) 7
  else (H.insert (p + 14) 2).insert (p + 0) 99

/-- **`HDRD`, one step:** the dispatch on BTYPE (acc): stored, fixed (fill index 0), dynamic, or "invalid block type". -/
theorem hdrd_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    Steps₂ (closeAt p hdrdT, σ) (.ret (.const (.cap p)), ⟨hdrdH σ.H p a, σ.R⟩) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  refine steps_run 12 ?_
  by_cases h0 : a = 0
  · subst h0
    simp [closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, mSHDR,
      show (2069 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
  by_cases h1 : a = 1
  · subst h1
    simp [closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, cFILL, mFIXLENS,
      show (2069 : Int) < L by omega, show (10 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
  by_cases h2 : a = 2
  · subst h2
    simp [closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, mDHDR,
      show (2069 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
  simp [closeAt, hdrdT, hdrdN, hdrdH, h0, h1, h2, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst,
    Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL,
    constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, cREASON, rBTYPE, mREJECT,
    show (2069 : Int) < L by omega, show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-! ## Stored blocks (S3, split at each field by S-8): `SHDR` aligns and requests LEN, `SLEN` keeps it and requests NLEN,
`SNLEN` makes S's three checks in S's order, `SCOPY` copies ONE byte per step and ends the block -/

def cM : Int := 3
def cPEND : Int := 5
def cOUTMAX : Int := 16
def mSLEN : Int := 8
def mSNLEN : Int := 9
def mSCOPY : Int := 10
def mDONE : Int := 98
def rSTORED : Int := 3   -- "invalid stored block lengths"
def rOVER : Int := 4     -- "overflow"

/-- `SHDR`: align the cursor (S1's `align`: to the next byte unless bit = 0), then request LEN (16 bits), ret `SLEN`. -/
def shdrN : NT :=
  .op "by" tint .load [.v "w", .i cBY] <|
  .op "bi" tint .load [.v "w", .i cBI] <|
  .letE "nb" tint (.ite (.p2 .eq (.v "bi") (.i 0)) (.ret (.v "by")) (.ret (.p2 .add (.v "by") (.i 1)))) <|
  .op "w1" tcap .store [.v "w", .i cBY, .v "nb"] <|
  .op "w2" tcap .store [.v "w1", .i cBI, .i 0] (reqN "w2" 16 mSLEN)
/-- `SLEN`: LEN is in acc; keep it as the pending count, then request NLEN (16 bits), ret `SNLEN`. -/
def slenN : NT :=
  .op "a" tint .load [.v "w", .i cACC] <|
  .op "w1" tcap .store [.v "w", .i cPEND, .v "a"] (reqN "w1" 16 mSNLEN)
/-- `SNLEN`: NLEN is in acc. S3's checks, in S3's order: NLEN = LEN ^ 0xFFFF (for 16-bit fields, NLEN + LEN = 65535), then
byte + LEN ≤ n ("truncated"), then m + LEN ≤ OUTMAX ("overflow"); all pass → `SCOPY`. -/
def snlenN : NT :=
  .op "a" tint .load [.v "w", .i cACC] <|
  .op "len" tint .load [.v "w", .i cPEND] <|
  .op "by" tint .load [.v "w", .i cBY] <|
  .op "n" tint .load [.v "w", .i cN] <|
  .op "m" tint .load [.v "w", .i cM] <|
  .op "om" tint .load [.v "w", .i cOUTMAX] <|
  .ite (.p2 .eq (.p2 .add (.v "a") (.v "len")) (.i 65535))
    (.ite (.p2 .lt (.v "n") (.p2 .add (.v "by") (.v "len")))
      (.op "w1" tcap .store [.v "w", .i cREASON, .i rTRUNC] (.op "w2" tcap .store [.v "w1", .i cMODE, .i mREJECT] (.ret (.v "w2"))))
      (.ite (.p2 .lt (.v "om") (.p2 .add (.v "m") (.v "len")))
        (.op "w1" tcap .store [.v "w", .i cREASON, .i rOVER] (.op "w2" tcap .store [.v "w1", .i cMODE, .i mREJECT] (.ret (.v "w2"))))
        (.op "w1" tcap .store [.v "w", .i cMODE, .i mSCOPY] (.ret (.v "w1")))))
    (.op "w1" tcap .store [.v "w", .i cREASON, .i rSTORED] (.op "w2" tcap .store [.v "w1", .i cMODE, .i mREJECT] (.ret (.v "w2"))))
/-- `SCOPY`: with pending 0 the block ends (BFINAL = 1 → `DONE`, else `HDR`); otherwise copy input[byte] to output[m]
(the output at `IN + n`), and advance byte, m and the pending count. -/
def scopyN : NT :=
  .op "k" tint .load [.v "w", .i cPEND] <|
  .ite (.p2 .eq (.v "k") (.i 0))
    (.op "bf" tint .load [.v "w", .i cBF] <|
     .ite (.p2 .eq (.v "bf") (.i 1))
       (.op "w1" tcap .store [.v "w", .i cMODE, .i mDONE] (.ret (.v "w1")))
       (.op "w1" tcap .store [.v "w", .i cMODE, .i mHDR] (.ret (.v "w1"))))
    (.op "by" tint .load [.v "w", .i cBY] <|
     .op "n" tint .load [.v "w", .i cN] <|
     .op "x" tint .load [.v "w", .p2 .add (.i IN) (.v "by")] <|
     .op "m" tint .load [.v "w", .i cM] <|
     .op "w1" tcap .store [.v "w", .p2 .add (.i IN) (.v "m"), .v "x"] <|
     .op "w2" tcap .store [.v "w1", .i cBY, .p2 .add (.v "by") (.i 1)] <|
     .op "w3" tcap .store [.v "w2", .i cM, .p2 .add (.v "m") (.i 1)] <|
     .op "w4" tcap .store [.v "w3", .i cPEND, .p2 .sub (.v "k") (.i 1)] (.ret (.v "w4")))

def shdrT : Tm₂ := shdrN.c ["w"]
def slenT : Tm₂ := slenN.c ["w"]
def snlenT : Tm₂ := snlenN.c ["w"]
def scopyT : Tm₂ := scopyN.c ["w"]

/-- **`SHDR`, one step:** the cursor aligned, then LEN requested (16 bits, ret `SLEN`). -/
theorem shdr_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bx bi : Int) (hby : f cBY = bx) (hbi : f cBI = bi) :
    Steps₂ (closeAt p shdrT, σ)
      (.ret (.const (.cap p)), ⟨reqH ((σ.H.insert (p + 1) (if bi = 0 then bx else bx + 1)).insert (p + 2) 0) p 16 8, σ.R⟩) := by
  simp only [cBY, cBI] at hby hbi
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  rw [hby] at h1; rw [hbi] at h2
  refine steps_run 16 ?_
  by_cases h0 : bi = 0
  · subst h0
    simp [shdrT, shdrN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h1, h2, cBY, cBI, cK, cACC, cWT, cRET, cMODE, mREAD, mSLEN,
      show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (2068 : Int) < L by omega,
      show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega]
  · simp [shdrT, shdrN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h0, h1, h2, cBY, cBI, cK, cACC, cWT, cRET, cMODE, mREAD, mSLEN,
      show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (2068 : Int) < L by omega,
      show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega]

/-- **`SLEN`, one step:** LEN (acc) becomes the pending count, and NLEN is requested (16 bits, ret `SNLEN`). -/
theorem slen_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    Steps₂ (closeAt p slenT, σ) (.ret (.const (.cap p)), ⟨reqH (σ.H.insert (p + 5) a) p 16 9, σ.R⟩) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  refine steps_run 10 ?_
  simp [slenT, slenN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hia, cK, cACC, cWT, cRET, cMODE, cPEND, mREAD, mSNLEN,
    show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega,
    show (2071 : Int) < L by omega, show (5 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-- The cells `SNLEN` writes: the reason and REJECT on a failed check, else mode `SCOPY`. -/
def snlenH (H : Finmap (fun _ : Int => Int)) (p a len bx n m om : Int) : Finmap (fun _ : Int => Int) :=
  if a + len = 65535 then
    if n < bx + len then (H.insert (p + 14) 1).insert (p + 0) 99
    else if om < m + len then (H.insert (p + 14) 4).insert (p + 0) 99
    else H.insert (p + 0) 10
  else (H.insert (p + 14) 3).insert (p + 0) 99

/-- **`SNLEN`, one step:** S3's three checks in S3's order, each to its own reason; all passing → `SCOPY`. -/
theorem snlen_step {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a len bx n m om : Int) (ha : f cACC = a) (hlen : f cPEND = len) (hby : f cBY = bx) (hn : f cN = n) (hm : f cM = m)
    (hom : f cOUTMAX = om) :
    Steps₂ (closeAt p snlenT, σ) (.ret (.const (.cap p)), ⟨snlenH σ.H p a len bx n m om, σ.R⟩) := by
  simp only [cACC, cPEND, cBY, cN, cM, cOUTMAX] at ha hlen hby hn hm hom
  have hia := hw.cell 2069 (by decide) (by omega)
  have h5 := hw.cell 5 (by decide) (by omega)
  have h1 := hw.cell 1 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have h3 := hw.cell 3 (by decide) (by omega)
  have h16 := hw.cell 16 (by decide) (by omega)
  rw [ha] at hia; rw [hlen] at h5; rw [hby] at h1; rw [hn] at h15; rw [hm] at h3; rw [hom] at h16
  refine steps_run 16 ?_
  by_cases hs : a + len = 65535
  · by_cases ht : n < bx + len
    · simp [snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX, cMODE,
        cREASON, rTRUNC, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
        show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
        show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
    · by_cases ho : om < m + len
      · simp [snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, ho, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX,
          cMODE, cREASON, rOVER, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega,
          show (1 : Int) < L by omega, show (15 : Int) < L by omega, show (3 : Int) < L by omega,
          show (16 : Int) < L by omega, show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
      · simp [snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, ho, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX,
          cMODE, mSCOPY, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
          show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
          show (0 : Int) < L by omega, show 0 < L by omega]
  · simp [snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX, cMODE,
      cREASON, rSTORED, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
      show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
      show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-- **`SCOPY`, the block's end (pending 0):** BFINAL = 1 → `DONE`, otherwise `HDR`; nothing else is written. -/
theorem scopy_end {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bf : Int) (hk : f cPEND = 0) (hbf : f cBF = bf) :
    Steps₂ (closeAt p scopyT, σ)
      (.ret (.const (.cap p)), ⟨σ.H.insert (p + 0) (if bf = 1 then 98 else 1), σ.R⟩) := by
  simp only [cPEND, cBF] at hk hbf
  have h5 := hw.cell 5 (by decide) (by omega)
  have h4 := hw.cell 4 (by decide) (by omega)
  rw [hk] at h5; rw [hbf] at h4
  refine steps_run 10 ?_
  by_cases h : bf = 1
  · subst h
    simp [scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h5, h4, cPEND, cBF, cMODE, mDONE, show (5 : Int) < L by omega,
      show (4 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]
  · simp [scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h, h5, h4, cPEND, cBF, cMODE, mHDR, show (5 : Int) < L by omega,
      show (4 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

/-- **`SCOPY`, one byte (pending k ≠ 0):** input[bx] is written at output[m] (cell `IN + n + m`), and byte, m and the
pending count advance. The bounds bx < n and m < OUTMAX are what `SNLEN`'s checks leave behind. -/
theorem scopy_byte {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (bx n m om : Nat) (k x : Int) (hL : 2080 + n + om ≤ L) (hk : f cPEND = k) (hk0 : k ≠ 0) (hby : f cBY = bx)
    (hn : f cN = n) (hbyn : bx < n) (hx : f (IN + bx) = x) (hm : f cM = m) (hmo : m < om) :
    Steps₂ (closeAt p scopyT, σ)
      (.ret (.const (.cap p)),
        ⟨(((σ.H.insert (p + (2080 + n + m)) x).insert (p + 1) (bx + 1)).insert (p + 3) (m + 1)).insert (p + 5) (k - 1),
          σ.R⟩) := by
  simp only [cPEND, cBY, cN, IN, cM] at hk hby hn hx hm
  have h5 := hw.cell 5 (by decide) (by omega)
  have h1 := hw.cell 1 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have hix := hw.cell (2080 + bx) (by omega) (by omega)
  have h3 := hw.cell 3 (by decide) (by omega)
  rw [hk] at h5; rw [hby] at h1; rw [hn] at h15; rw [hx] at hix; rw [hm] at h3
  refine steps_run 16 ?_
  simp [scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, run₂, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hk0, h5, h1, h15, hix, h3, cPEND, cBY, cN, IN, cM,
    show (5 : Int) < L by omega, show (1 : Int) < L by omega, show (15 : Int) < L by omega,
    show (3 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
    show (2080 : Int) + n + m < L by omega, show (0 : Int) ≤ 2080 + n + m by omega,
    show (0 : Int) < L by omega, show 0 < L by omega]

end VIRDeflate.StepSc
