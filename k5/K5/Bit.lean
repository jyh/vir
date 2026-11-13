/-
  O95, K5-2 (STATUS-vir 295), TABLE's BITc call on the checked runner. `Reach c d`: a CHECKED run from `c` reaches `d`
  (every configuration it leaves passes `headB`). It composes (`trans`), lifts under a `let` frame (`letE`), and gives
  `SrcInRange c` from `SrcInRange d`. POW, STRIP and BITc are proved to `Reach` their results by the same induction as
  Step.lean's `pow2_steps` / `strip_steps` / `bit_steps`, with every intermediate atom in range (k ≤ 7, 0 ≤ v < 256).
-/
import K5.Checked

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

local notation "cI" => VIRDeflate.Step.ci
local notation "vR" => VIRDeflate.Step.vr

inductive Reach : Config → Config → Prop
  | refl (c : Config) : Reach c c
  | step {c c' d : Config} : headB c.1 = true → stepFn₂ c.1 c.2 = some c' → Reach c' d → Reach c d

theorem Reach.trans {c d e : Config} (h₁ : Reach c d) (h₂ : Reach d e) : Reach c e := by
  induction h₁ with
  | refl => exact h₂
  | step hb hs _ ih => exact .step hb hs (ih h₂)

theorem Reach.srcInRange {c d : Config} (h : Reach c d) (hd : SrcInRange d) : SrcInRange c := by
  induction h with
  | refl => exact hd
  | step hb hs _ ih => exact srcInRange_step hb (by simp [hs]) (by simpa [hs] using ih hd)

theorem reach_runC : ∀ (k : Nat) (c : Config), Reach c (run₂C k c)
  | 0, c => .refl c
  | k + 1, c => by
      simp only [run₂C]
      cases hc : stepFn₂C c.1 c.2 with
      | none => exact .refl c
      | some c' =>
        simp only [stepFn₂C] at hc
        split at hc
        · rename_i hb; exact .step hb hc (reach_runC k c')
        · cases hc

theorem reach_of_runC {k : Nat} {c d : Config} (h : run₂C k c = d) : Reach c d := h ▸ reach_runC k c

theorem stepFn₂_letE {τ : Ty₂} {e₁ e₂ : Tm₂} {σ : Store} {c' : Config} (h : stepFn₂ e₁ σ = some c') :
    stepFn₂ (.letE τ e₁ e₂) σ = some (.letE τ c'.1 e₂, c'.2) := by
  cases e₁ with
  | ret a => simp [stepFn₂, stepFn] at h
  | _ =>
    rw [show stepFn₂ (.letE τ _ e₂) σ = (stepFn₂ _ σ).map (fun c => (.letE τ c.1 e₂, c.2)) from rfl, h]; rfl

/-- The `let` frame: a checked run of `e₁` is a checked run of `let x = e₁ in e₂` (headB of a `let` IS its bound term's). -/
theorem Reach.letE {τ : Ty₂} {e₂ : Tm₂} {c d : Config} (h : Reach c d) :
    Reach (.letE τ c.1 e₂, c.2) (.letE τ d.1 e₂, d.2) := by
  induction h with
  | refl => exact .refl _
  | step hb hs _ ih => exact .step (by simpa [headB] using hb) (stepFn₂_letE hs) ih

macro "l2evalC" : tactic => `(tactic| simp (disch := omega) [STRIPc, stripTop, run₂C, stepFn₂C, headB, aInR, aInRL, cInR,
  inRange_eq, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool,
  Tm.subst, Atom.subst, Atom.substL, POW, STRIP, ple, plt, psub, pmul, padd, S₂, *])

theorem pow_le_128 {k : Nat} (hk : k ≤ 7) : (2 : Int) ^ k ≤ 128 := by
  calc (2 : Int) ^ k ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hk
    _ = 128 := by norm_num

theorem pow2_reach0 (a : Atom₂) (ha : Atom.eval a = some (cI 0)) (hra : aInR a = true) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    Reach (.letE τ (.app POW a) e₂, σ) (e₂.subst 0 (cI 1), σ) :=
  reach_of_runC (k := 3) (by l2evalC)

theorem pow2_reachA (k : Nat) (hk : k + 1 ≤ 7) (a : Atom₂) (ha : Atom.eval a = some (cI ((k + 1 : Nat) : Int)))
    (hra : aInR a = true) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 2 (.letE τ (.app POW a) e₂, σ) =
      (.letE τ (.letE tint (.app POW (psub (cI ((k + 1 : Nat) : Int)) (cI 1))) (.ret (pmul (cI 2) (vR 0)))) e₂, σ) := by
  have hk0 : ¬ ((k : Int) + 1 ≤ 0) := by omega
  l2evalC

theorem pow2_reachC (v : Int) (h0 : 0 < v) (h1 : v ≤ 64) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 1 (.letE τ ((Tm.ret (pmul (cI 2) (vR 0))).subst 0 (cI v)) e₂, σ) = (e₂.subst 0 (cI (2 * v)), σ) := by
  l2evalC

/-- **`pow2`, checked:** for `a` evaluating to `k ≤ 7`, `let x = POW(a) in e₂` reaches `e₂[2^k/x]` by a checked run. -/
theorem pow2_reach (k : Nat) (hk : k ≤ 7) : ∀ (a : Atom₂), Atom.eval a = some (cI k) → aInR a = true →
    ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store), Reach (.letE τ (.app POW a) e₂, σ) (e₂.subst 0 (cI (2 ^ k)), σ) := by
  induction k with
  | zero =>
    intro a ha hra τ e₂ σ
    simpa using pow2_reach0 a (by simpa using ha) hra τ e₂ σ
  | succ k ih =>
    intro a ha hra τ e₂ σ
    refine Reach.trans (reach_of_runC (pow2_reachA k hk a ha hra τ e₂ σ)) ?_
    refine Reach.trans (Reach.letE (τ := τ) (e₂ := e₂)
      (ih (by omega) (psub (cI ((k + 1 : Nat) : Int)) (cI 1)) (by l2evalC) (by l2evalC) tint
        (.ret (pmul (cI 2) (vR 0))) σ)) ?_
    have h1 := pow_le_128 (k := k + 1) hk
    have h0 : (0 : Int) < 2 ^ k := by positivity
    have h2 : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2]
    exact reach_of_runC (pow2_reachC (2 ^ k) h0 (by omega) τ e₂ σ)

theorem strip_reach0 (i : Nat) (v : Int) (a : Atom₂) (ha : Atom.eval a = some (.pair (.pair (cI 0) (cI i)) (cI v)))
    (hra : aInR a = true) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 3 (.letE τ (.app STRIPc a) e₂, σ) = (e₂.subst 0 (cI v), σ) := by
  l2evalC

/-- The inner state after STRIP's call and test (n+1 > 0): `let p = pow2(i + (n+1)) in K n i v`. -/
def stripK (n i : Nat) (v : Int) : Tm₂ :=
  .letE tint (.ite (plt (.snd (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v))) (vR 0))
      (.ret (.snd (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v))))
      (.ret (psub (.snd (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v))) (vR 0))))
    (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v)))) (cI 1)) (.snd (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v))))) (vR 0)))

theorem strip_reachA (n i : Nat) (hin : i + (n + 1) ≤ 7) (v : Int) (hv0 : 0 ≤ v) (hv : v < 256) (a : Atom₂)
    (ha : Atom.eval a = some (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v))) (hra : aInR a = true)
    (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 2 (.letE τ (.app STRIPc a) e₂, σ) =
      (.letE τ (.letE tint (.app POW (padd (.snd (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v)))) (.fst (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v)))))) (stripK n i v)) e₂, σ) := by
  have hk0 : ¬ ((n : Int) + 1 ≤ 0) := by omega
  simp only [stripK]
  l2evalC

theorem strip_reachB (n i : Nat) (hin : i + (n + 1) ≤ 7) (v p : Int) (hv0 : 0 ≤ v) (hv : v < 256) (hp0 : 0 < p) (hp : p ≤ 128)
    (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 2 (.letE τ ((stripK n i v).subst 0 (cI p)) e₂, σ) =
      (.letE τ (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v)))) (cI 1)) (.snd (.fst (.pair (.pair (cI ((n + 1 : Nat) : Int)) (cI i)) (cI v)))))
        (cI (if v < p then v else v - p)))) e₂, σ) := by
  simp only [stripK]
  by_cases hvp : v < p
  · have : decide (v < p) = true := by simp [hvp]
    l2evalC
  · have : decide (v < p) = false := by simp [hvp]
    l2evalC

/-- **`strip`, checked:** for `a` evaluating to `((n, i), v)`, i + n ≤ 7, 0 ≤ v < 256, `let x = STRIPc(a) in e₂` reaches
`e₂[stripTop n i v / x]` by a checked run. -/
theorem strip_reach (n i : Nat) : i + n ≤ 7 → ∀ (v : Int), 0 ≤ v → v < 256 → ∀ (a : Atom₂),
    Atom.eval a = some (.pair (.pair (cI n) (cI i)) (cI v)) → aInR a = true → ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store),
    Reach (.letE τ (.app STRIPc a) e₂, σ) (e₂.subst 0 (cI (stripTop n i v)), σ) := by
  induction n with
  | zero =>
    intro _ v _ _ a ha hra τ e₂ σ
    simpa [stripTop] using reach_of_runC (strip_reach0 i v a (by simpa using ha) hra τ e₂ σ)
  | succ n ih =>
    intro hin v hv0 hv a ha hra τ e₂ σ
    refine Reach.trans (reach_of_runC (strip_reachA n i hin v hv0 hv a ha hra τ e₂ σ)) ?_
    refine Reach.trans (Reach.letE (τ := τ) (e₂ := e₂) (pow2_reach (i + (n + 1)) hin _
      (by l2evalC <;> push_cast <;> ring_nf) (by l2evalC) tint (stripK n i v) σ)) ?_
    have hp := pow_le_128 (k := i + (n + 1)) hin
    have hp0 : (0 : Int) < 2 ^ (i + (n + 1)) := by positivity
    refine Reach.trans (reach_of_runC (strip_reachB n i hin v _ hv0 hv hp0 hp τ e₂ σ)) ?_
    have hstep : stripTop (n + 1) i v =
        stripTop n i (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) := by
      simp only [stripTop, pow2_eq, Nat.add_assoc]
    rw [hstep]
    have hw0 : 0 ≤ (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) := by split_ifs <;> omega
    have hw : (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) < 256 := by split_ifs <;> omega
    exact ih (by omega) _ hw0 hw _ (by l2evalC) (by l2evalC) τ e₂ σ

theorem stripTop_rng : ∀ (n i : Nat) (v : Int), 0 ≤ v → v < 256 → 0 ≤ stripTop n i v ∧ stripTop n i v < 256
  | 0, _, v, h0, h1 => by simp [stripTop]; omega
  | n + 1, i, v, h0, h1 => by
      simp only [stripTop]
      have hp : 0 < pow2 (i + n + 1) := by rw [pow2_eq]; positivity
      apply stripTop_rng n i
      · split_ifs <;> omega
      · split_ifs <;> omega

/-- BITc's body after the call: `let q = pow2(i) in if r < q then 0 else 1`, with r already bound. -/
def bitK (b : Int) (i : Nat) : Tm₂ :=
  .letE tint (.app POW (.snd (.pair (cI b) (cI (i : Int))))) (.ite (plt (vR 1) (vR 0)) (.ret (cI 0)) (.ret (cI 1)))

def bitK2 (r : Int) : Tm₂ := .ite (plt (cI r) (vR 0)) (.ret (cI 0)) (.ret (cI 1))

theorem bitK_subst (b r : Int) (i : Nat) : (bitK b i).subst 0 (cI r) = .letE tint (.app POW (.snd (.pair (cI b) (cI (i : Int))))) (bitK2 r) := by
  simp [bitK, bitK2, Tm.subst, Atom.subst, Atom.substL, POW, plt, ple, psub, pmul]

theorem bit_reachA (b : Int) (i : Nat) (a : Atom₂) (ha : Atom.eval a = some (.pair (cI b) (cI (i : Int)))) (hra : aInR a = true)
    (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 1 (.letE τ (.app BITc a) e₂, σ) =
      (.letE τ (.letE tint (.app STRIPc (.pair (.pair (psub (cI 7) (.snd (.pair (cI b) (cI (i : Int))))) (.snd (.pair (cI b) (cI (i : Int))))) (.fst (.pair (cI b) (cI (i : Int)))))) (bitK b i)) e₂, σ) := by
  simp only [bitK]
  simp only [BITc] 
  l2evalC

theorem bit_reachC (r q : Int) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    run₂C 2 (.letE τ ((bitK2 r).subst 0 (cI q)) e₂, σ) = (e₂.subst 0 (cI (if r < q then 0 else 1)), σ) := by
  simp only [bitK2]
  by_cases h : r < q
  · have : decide (r < q) = true := by simp [h]
    simp only [if_pos h]; l2evalC
  · have : decide (r < q) = false := by simp [h]
    simp only [if_neg h]; l2evalC

/-- **The step's bit call, checked:** for `a` evaluating to `(b, i)`, 0 ≤ b < 256, i ≤ 7, `let x = BITc(a) in e₂` reaches
`e₂[bitAt b i / x]` by a checked run. -/
theorem bit_reach (b : Int) (i : Nat) (hb0 : 0 ≤ b) (hb : b < 256) (hi : i ≤ 7) (a : Atom₂)
    (ha : Atom.eval a = some (.pair (cI b) (cI (i : Int)))) (hra : aInR a = true) (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    Reach (.letE τ (.app BITc a) e₂, σ) (e₂.subst 0 (cI (bitAt b i)), σ) := by
  refine Reach.trans (reach_of_runC (bit_reachA b i a ha hra τ e₂ σ)) ?_
  refine Reach.trans (Reach.letE (τ := τ) (e₂ := e₂) (strip_reach (7 - i) i (by omega) b hb0 hb _
    (by l2evalC <;> omega) (by l2evalC <;> omega) tint (bitK b i) σ)) ?_
  rw [bitK_subst]
  refine Reach.trans (Reach.letE (τ := τ) (e₂ := e₂) (pow2_reach i hi _ (by l2evalC) (by l2evalC) tint
    (bitK2 (stripTop (7 - i) i b)) σ)) ?_
  refine Reach.trans (reach_of_runC (bit_reachC _ _ τ e₂ σ)) ?_
  unfold bitAt
  rw [pow2_eq]
  exact .refl _

end K5
