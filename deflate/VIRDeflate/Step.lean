/-
OBJECT-DEFLATE under X1 (a): the L2 step program (DECLARATIONS-DEFLATE.md, "The L2 step program", S-1 … S-6, declared before this
file). This file grows per row. FIRST: D4's bit-of-a-byte as an L2 term, a pure top-level `fix` over `Int` with `sub`, `lt`,
`le`, `add` and `mul` only (P unchanged), run by L2's own step function and proved equal to `bitAt` (Bits.lean) on every byte.
l1/ and l2/ are imported and never edited (D2).
-/
import VIRDeflate.Bits
import VIRL2

namespace VIRDeflate.Step
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

end VIRDeflate.Step
