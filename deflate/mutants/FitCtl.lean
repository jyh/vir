/-
OBJECT-DEFLATE under X1 (a): Safety's first piece (STATUS-vir 293 (b)): every mode's one-step lemma, a relational `Steps₂`, is
turned into the FUNCTIONAL step `stepS` of Statements.lean, which runs at most KSTEP = 512 L2 steps.
- A counted ⟶₂* (`StepsN`), and `stepFn₂` COMPLETE for ⟶₂ (l2 proves it sound; L1's completeness is l2's `stepFn_complete`).
  So a counted path to a terminal configuration is what `run₂` computes at any fuel at or above the count.
- A path-length measure `plen` (a `let` adds its two sides, an `if` the longer branch; atoms count nothing). Every step of an
  APP-FREE term decreases it and keeps the term app-free, so a path from an app-free term is no longer than its `plen`.
- The dispatch, counted: at most 1 + 28 steps from the step term to a mode term's closed form.
⇒ `stepS_of_mode`: for every mode term that is app-free with `plen ≤ 483`, its one-step lemma gives `stepS p σ = some σ'`.
`modes_fit` checks the 27 modes other than TABLE (whose one `BITc` call is counted separately). No program code here.
-/
import VIRDeflate.Statements
-- CONTROL: Fit.lean verbatim. Must be GREEN.

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## Counted steps -/

inductive StepsN : Nat → Config → Config → Prop where
  | refl (c : Config) : StepsN 0 c c
  | step {n : Nat} {c c' c'' : Config} : Step₂ c c' → StepsN n c' c'' → StepsN (n + 1) c c''

theorem StepsN.trans {a b : Nat} {c₁ c₂ c₃ : Config} (h₁ : StepsN a c₁ c₂) (h₂ : StepsN b c₂ c₃) :
    StepsN (a + b) c₁ c₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | @step n c c' c'' s _ ih => rw [show n + 1 + b = (n + b) + 1 by omega]; exact .step s (ih h₂)

theorem stepsN_of_steps {c d : Config} (h : Steps₂ c d) : ∃ n, StepsN n c d := by
  induction h with
  | refl c => exact ⟨0, .refl c⟩
  | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step s hn⟩

/-! ## `stepFn₂` is complete for ⟶₂ -/

theorem pure_complete {e e' : Tm₂} (h : Step e e') (σ : Store) : stepFn₂ e σ = some (e', σ) := by
  induction h with
  | letRet ha => simp [stepFn₂, ha]
  | @letStep τ e₁ e₁' e₂ hs ih =>
    cases e₁ with
    | ret a => cases hs
    | letOp => cases hs
    | _ => show Option.map _ (stepFn₂ _ _) = _; rw [ih]; rfl
  | appLam h₁ h₂ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.appLam h₁ h₂)]; rfl
  | appFix h₁ h₂ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.appFix h₁ h₂)]; rfl
  | iteT h₁ h₂ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.iteT h₁ h₂)]; rfl
  | iteF h₁ h₂ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.iteF h₁ h₂)]; rfl
  | caseL h₁ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.caseL h₁)]; rfl
  | caseR h₁ => show Option.map _ (stepFn _) = _; rw [stepFn_complete (.caseR h₁)]; rfl

theorem stepFn₂_complete {c c' : Config} (h : Step₂ c c') : stepFn₂ c.1 c.2 = some c' := by
  induction h with
  | pure hs => exact pure_complete hs _
  | @letStep τ e₁ e₁' e₂ σ σ' hs ih =>
    have ih' : stepFn₂ e₁ σ = some (e₁', σ') := ih
    cases e₁ with
    | ret a => cases hs with | pure h' => cases h'
    | _ => show Option.map _ (stepFn₂ _ _) = _; rw [ih']; rfl
  | op h₁ h₂ => simp [stepFn₂, h₁, h₂]

theorem run₂_succ_of {c c' : Config} (h : stepFn₂ c.1 c.2 = some c') (m : Nat) : run₂ (m + 1) c = run₂ m c' := by
  simp [run₂, h]

theorem run₂_stuck {d : Config} (h : stepFn₂ d.1 d.2 = none) : ∀ m, run₂ m d = d
  | 0 => rfl
  | m + 1 => by simp [run₂, h]

/-- A counted path to a stuck configuration is what `run₂` computes at every fuel at or above the count. -/
theorem run₂_of_stepsN {n : Nat} {c d : Config} (h : StepsN n c d) (hd : stepFn₂ d.1 d.2 = none) :
    ∀ m, n ≤ m → run₂ m c = d := by
  induction h with
  | refl => intro m _; exact run₂_stuck hd m
  | @step n c c' c'' s _ ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [run₂_succ_of (stepFn₂_complete s)]
    exact ih hd m' (by omega)

theorem stepsN_of_run : ∀ (n : Nat) (c : Config), ∃ k ≤ n, StepsN k c (run₂ n c)
  | 0, c => ⟨0, le_refl _, .refl c⟩
  | n + 1, ⟨e, σ⟩ => by
    cases h : stepFn₂ e σ with
    | none => exact ⟨0, by omega, by rw [run₂_stuck (d := (e, σ)) h]; exact .refl _⟩
    | some c' =>
      obtain ⟨k, hk, hs⟩ := stepsN_of_run n c'
      exact ⟨k + 1, by omega, by rw [run₂_succ_of (c := (e, σ)) h]; exact .step (stepFn₂_sound h) hs⟩

theorem stepsN_run {c d : Config} (n : Nat) (h : run₂ n c = d) : ∃ k ≤ n, StepsN k c d := h ▸ stepsN_of_run n c

/-! ## The path-length measure -/

def plen : Tm₂ → Nat
  | .ret _ => 0
  | .letE _ e₁ e₂ => plen e₁ + 1 + plen e₂
  | .letOp _ _ _ e => plen e + 1
  | .app _ _ => 0
  | .ite _ e₁ e₂ => max (plen e₁) (plen e₂) + 1
  | .case _ e₁ e₂ => max (plen e₁) (plen e₂) + 1

def appFree : Tm₂ → Bool
  | .ret _ => true
  | .letE _ e₁ e₂ => appFree e₁ && appFree e₂
  | .letOp _ _ _ e => appFree e
  | .app _ _ => false
  | .ite _ e₁ e₂ => appFree e₁ && appFree e₂
  | .case _ e₁ e₂ => appFree e₁ && appFree e₂

theorem plen_subst : ∀ (e : Tm₂) (k : Nat) (v : Atom₂), plen (e.subst k v) = plen e ∧ appFree (e.subst k v) = appFree e
  | .ret _, _, _ => by simp [Tm.subst, plen, appFree]
  | .letE _ e₁ e₂, k, v => by
    have h₁ := plen_subst e₁ k v; have h₂ := plen_subst e₂ (k + 1) v
    simp [Tm.subst, plen, appFree, h₁.1, h₁.2, h₂.1, h₂.2]
  | .letOp _ _ _ e, k, v => by
    have h := plen_subst e (k + 1) v
    simp [Tm.subst, plen, appFree, h.1, h.2]
  | .app _ _, _, _ => by simp [Tm.subst, plen, appFree]
  | .ite _ e₁ e₂, k, v => by
    have h₁ := plen_subst e₁ k v; have h₂ := plen_subst e₂ k v
    simp [Tm.subst, plen, appFree, h₁.1, h₁.2, h₂.1, h₂.2]
  | .case _ e₁ e₂, k, v => by
    have h₁ := plen_subst e₁ (k + 1) v; have h₂ := plen_subst e₂ (k + 1) v
    simp [Tm.subst, plen, appFree, h₁.1, h₁.2, h₂.1, h₂.2]

theorem pure_dec {e e' : Tm₂} (h : Step e e') : appFree e = true → plen e' < plen e ∧ appFree e' = true := by
  induction h with
  | @letRet τ a v e₂ _ =>
    intro hf
    simp only [plen, appFree, Bool.true_and] at hf ⊢
    rw [(plen_subst e₂ 0 v).1, (plen_subst e₂ 0 v).2]
    exact ⟨by omega, hf⟩
  | @letStep τ e₁ e₁' e₂ _ ih =>
    intro hf
    simp only [plen, appFree, Bool.and_eq_true] at hf ⊢
    obtain ⟨h1, h2⟩ := ih hf.1
    exact ⟨by omega, h2, hf.2⟩
  | appLam => intro hf; simp [appFree] at hf
  | appFix => intro hf; simp [appFree] at hf
  | iteT =>
    intro hf; simp only [plen, appFree, Bool.and_eq_true] at hf ⊢; exact ⟨by omega, hf.1⟩
  | iteF =>
    intro hf; simp only [plen, appFree, Bool.and_eq_true] at hf ⊢; exact ⟨by omega, hf.2⟩
  | @caseL a e₁ e₂ τ v _ =>
    intro hf; simp only [plen, appFree, Bool.and_eq_true] at hf ⊢
    rw [(plen_subst e₁ 0 v).1, (plen_subst e₁ 0 v).2]; exact ⟨by omega, hf.1⟩
  | @caseR a e₁ e₂ τ v _ =>
    intro hf; simp only [plen, appFree, Bool.and_eq_true] at hf ⊢
    rw [(plen_subst e₂ 0 v).1, (plen_subst e₂ 0 v).2]; exact ⟨by omega, hf.2⟩

theorem step₂_dec {c c' : Config} (h : Step₂ c c') : appFree c.1 = true → plen c'.1 < plen c.1 ∧ appFree c'.1 = true := by
  induction h with
  | pure hs => exact pure_dec hs
  | @letStep τ e₁ e₁' e₂ σ σ' _ ih =>
    intro hf
    simp only [plen, appFree, Bool.and_eq_true] at hf ⊢
    have h1 : plen e₁' < plen e₁ := (ih hf.1).1
    have h2 : appFree e₁' = true := (ih hf.1).2
    exact ⟨by omega, h2, hf.2⟩
  | @op o as τ e vs v σ σ' _ _ =>
    intro hf
    simp only [plen, appFree] at hf ⊢
    rw [(plen_subst e 0 v).1, (plen_subst e 0 v).2]
    exact ⟨by omega, hf⟩

/-- **A path from an app-free term is no longer than its `plen`.** -/
theorem stepsN_le {n : Nat} {c d : Config} (h : StepsN n c d) : appFree c.1 = true → n ≤ plen c.1 := by
  induction h with
  | refl => intro; exact Nat.zero_le _
  | step s _ ih => intro hf; obtain ⟨h1, h2⟩ := step₂_dec s hf; have := ih h2; omega

/-! ## The dispatch, counted (Dispatch.lean's `disp_run` and `step_dispatch`, with each `run₂` kept as its count) -/

theorem disp_runN (p m : Int) (σ : Store) : ∀ (ms : List (Int × NT)), (∀ kt ∈ ms, NT.ok "md" kt.2) →
    ∃ k ≤ ms.length, StepsN k (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ms).c ["md", "w"])), σ)
      (match ms.lookup m with
       | some t => (closeAt p (t.c ["w"]), σ)
       | none => (.ret (capA p), σ))
  | [], _ => by
    refine ⟨0, le_refl _, ?_⟩
    simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, List.lookup]
    exact .refl _
  | (k, t) :: r, h => by
    have ht := carry_top p m t (h (k, t) (by simp))
    by_cases hk : m = k
    · subst hk
      have : Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ((m, t) :: r)).c ["md", "w"])) =
          Tm.ite (Atom.prim L1.Prim.eq [ci m, ci m]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))) := by
        rw [← ht]; simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL]
      rw [this]
      simp only [List.lookup, beq_self_eq_true]
      obtain ⟨j, hj, hs⟩ := stepsN_run 1 (c := (Tm.ite (Atom.prim L1.Prim.eq [ci m, ci m]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))), σ)) (d := (closeAt p (t.c ["w"]), σ))
        (by simp [run₂, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1,
          Const.ofL1, Const.toBool])
      exact ⟨j, by simp; omega, hs⟩
    · have : Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ((k, t) :: r)).c ["md", "w"])) =
          Tm.ite (Atom.prim L1.Prim.eq [ci m, ci k]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))) := by
        rw [← ht]; simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL]
      rw [this]
      have hb : (m == k) = false := by simp [hk]
      have hl : ((k, t) :: r).lookup m = r.lookup m := by simp [List.lookup, hb]
      rw [hl]
      obtain ⟨j, hj, hs⟩ := stepsN_run 1 (c := (Tm.ite (Atom.prim L1.Prim.eq [ci m, ci k]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))), σ))
        (d := (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"])), σ))
        (by simp [run₂, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
          Const.toL1, Const.ofL1, Const.toBool, hk])
      obtain ⟨j₂, hj₂, hs₂⟩ := disp_runN p m σ r (fun kt hkt => h kt (by simp [hkt]))
      exact ⟨j + j₂, by simp; omega, hs.trans hs₂⟩

theorem modes_length : modes.length = 28 := rfl

theorem step_dispatchN {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) (m : Int)
    (hm : f cMODE = m) :
    ∃ k ≤ 29, StepsN k (closeAt p stepT, σ)
      (match modes.lookup m with
       | some t => (closeAt p (t.c ["w"]), σ)
       | none => (.ret (capA p), σ)) := by
  simp only [cMODE] at hm
  have g0 := hw.get (i := 0) (by decide) (by omega) hm
  obtain ⟨j, hj, hs⟩ := stepsN_run 1 (c := (closeAt p stepT, σ))
    (d := (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN modes).c ["md", "w"])), σ)) (by
    simp only [closeAt, stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, run₂, stepFn₂, opStep, Store.load, hw.reg, g0, cMODE, capA]
    simp [NA.c, List.idxOf, List.findIdx, List.findIdx.go, Atom.substL, Atom.subst, Atom.eval, Atom.evalL, Store.load,
      hw.reg, hL, show (0 : Int) < L by omega, g0])
  obtain ⟨j₂, hj₂, hs₂⟩ := disp_runN p m σ modes modes_ok
  rw [modes_length] at hj₂
  exact ⟨j + j₂, by omega, hs.trans hs₂⟩

/-! ## The fit -/

/-- **A mode's one-step lemma is a `stepS`:** for a mode term that is app-free with `plen ≤ KSTEP − 29`, the relational step to
`ret ⟨p⟩` with store σ' is the functional step of Statements.lean. -/
theorem stepS_of_mode {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) {k : Int} {t : NT}
    (hm : f cMODE = k) (hk : modes.lookup k = some t) (hfree : appFree (t.c ["w"]) = true)
    (hlen : plen (t.c ["w"]) ≤ KSTEP - 29) {σ' : Store}
    (h : Steps₂ (closeAt p (t.c ["w"]), σ) (.ret (.const (.cap p)), σ')) : stepS p σ = some σ' := by
  obtain ⟨k₁, hk₁, h₁⟩ := step_dispatchN hw hL k hm
  rw [hk] at h₁
  obtain ⟨k₂, h₂⟩ := stepsN_of_steps h
  have hb := stepsN_le h₂ (by simpa [closeAt, (plen_subst _ _ _).2] using hfree)
  simp only [closeAt, (plen_subst _ _ _).1] at hb
  have hrun := run₂_of_stepsN (h₁.trans h₂) rfl KSTEP (by simp only [KSTEP] at hlen ⊢; omega)
  unfold stepS
  rw [hrun]
  simp

/-- The 27 modes other than TABLE are app-free and fit: `plen ≤ 483`. -/
theorem modes_fit : ∀ kt ∈ modes, kt.1 ≠ mTABLE → appFree (kt.2.c ["w"]) = true ∧ plen (kt.2.c ["w"]) ≤ KSTEP - 29 := by
  intro kt hkt hne
  simp only [modes, List.mem_cons, List.mem_nil_iff, or_false] at hkt
  rcases hkt with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h
  · exact absurd rfl hne
  all_goals simp [KSTEP, plen, appFree, NT.c, hdrN, readN, hdrbN, hdrdN, shdrN, fixlensN, dhdrN, slenN, snlenN, scopyN,
    buildN, lensN, symN, decodeN, symdN, lenxN, dstdN, dstxN, copyN, dh2N, dh3N, dh4N, clreadN, clputN, lsymN, lrepN, repN,
    reqN, reqDecN, reqKN, rejN, bZeroN, bCountN, bNextN, bRestN, bLeftN, bSymsN]


/-! ## TABLE's one `BITc` call, counted (Step.lean's `pow2_steps`, `strip_steps`, `bit_steps`, `table_step`, each `run₂` kept as
its count). The recursion is bounded by the bit index: POW ≤ 3k + 3, STRIP ≤ 3 + 31n with i + n ≤ 7, BIT ≤ 250, TABLE ≤ 262. -/

theorem StepsN.letE {n : Nat} {τ : Ty₂} {e₁ e₁' e₂ : Tm₂} {σ σ' : Store} (h : StepsN n (e₁, σ) (e₁', σ')) :
    StepsN n (.letE τ e₁ e₂, σ) (.letE τ e₁' e₂, σ') := by
  generalize hc : (e₁, σ) = c at h
  generalize hc' : (e₁', σ') = c' at h
  induction h generalizing e₁ σ with
  | refl => subst hc; cases hc'; exact .refl _
  | @step n c₁ c₂ c₃ s _ ih =>
    subst hc
    obtain ⟨e₂', σ₂⟩ := c₂
    exact .step (.letStep s) (ih rfl hc')

theorem stepsN_le_run {c d : Config} {B : Nat} (n : Nat) (hB : n ≤ B) (h : run₂ n c = d) : ∃ k ≤ B, StepsN k c d := by
  obtain ⟨k, hk, hs⟩ := stepsN_run n h
  exact ⟨k, by omega, hs⟩

theorem pow2_stepsN (k : Nat) : ∀ (a : Atom₂), Atom.eval a = some (ci k) → ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store),
    ∃ m ≤ 3 * k + 3, StepsN m (.letE τ (.app POW a) e₂, σ) (e₂.subst 0 (ci (2 ^ k)), σ) := by
  induction k with
  | zero =>
    intro a ha τ e₂ σ
    exact stepsN_le_run 3 (by omega) (by l2eval)
  | succ k ih =>
    intro a ha τ e₂ σ
    obtain ⟨m₁, hm₁, h₁⟩ := stepsN_run 2 (c := (.letE τ (.app POW a) e₂, σ))
      (d := (.letE τ (.letE tint (.app POW (psub (ci ((k + 1 : Nat) : Int)) (ci 1))) (.ret (pmul (ci 2) (vr 0)))) e₂, σ))
      (by l2eval; rw [show decide ((k : Int) < 0) = false by simp]; l2eval)
    obtain ⟨m₂, hm₂, h₂⟩ := ih (psub (ci ((k + 1 : Nat) : Int)) (ci 1)) (by l2eval) tint (.ret (pmul (ci 2) (vr 0))) σ
    obtain ⟨m₃, hm₃, h₃⟩ := stepsN_run 1
      (c := (.letE τ ((Tm.ret (pmul (ci 2) (vr 0))).subst 0 (ci (2 ^ k))) e₂, σ))
      (d := (e₂.subst 0 (ci (2 ^ (k + 1))), σ)) (by l2eval; ring_nf)
    exact ⟨m₁ + m₂ + m₃, by omega, (h₁.trans (StepsN.letE h₂)).trans h₃⟩

theorem strip_stepsN (n i : Nat) : i + n ≤ 7 → ∀ (v : Int) (a : Atom₂),
    Atom.eval a = some (.pair (.pair (ci n) (ci i)) (ci v)) → ∀ (τ : Ty₂) (e₂ : Tm₂) (σ : Store),
    ∃ m ≤ 3 + 31 * n, StepsN m (.letE τ (.app STRIPc a) e₂, σ) (e₂.subst 0 (ci (stripTop n i v)), σ) := by
  induction n with
  | zero =>
    intro _ v a ha τ e₂ σ
    exact stepsN_le_run 3 (by omega) (by l2eval)
  | succ n ih =>
    intro hin v a ha τ e₂ σ
    obtain ⟨m₁, hm₁, h₁⟩ := stepsN_run 2 (c := (.letE τ (.app STRIPc a) e₂, σ))
      (d := (.letE τ (.letE tint (.app POW (padd (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))))) (.letE tint (.ite (plt (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)) (.ret (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (.ret (psub (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)))) (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (vr 0))))) e₂, σ))
      (by clear ih; l2eval; all_goals (rw [show decide ((n : Int) < 0) = false by simp]; l2eval))
    obtain ⟨m₂, hm₂, h₂⟩ := pow2_stepsN (i + (n + 1)) (padd (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))))
      (by clear ih; l2eval; all_goals (push_cast; ring_nf)) tint (.letE tint (.ite (plt (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)) (.ret (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (.ret (psub (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)))) (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (vr 0)))) σ
    obtain ⟨m₃, hm₃, h₃⟩ := stepsN_run 2
      (c := (.letE τ (Tm.subst 0 (ci (2 ^ (i + (n + 1)))) (.letE tint (.ite (plt (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)) (.ret (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (.ret (psub (.snd (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))) (vr 0)))) (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (vr 0))))) e₂, σ))
      (d := (.letE τ (.app STRIPc (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (ci (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1)))))) e₂, σ))
      (by clear ih; by_cases hv : v < 2 ^ (i + (n + 1)) <;> l2eval <;>
        (rw [show decide (v < 2 ^ (i + (n + 1))) = false from decide_eq_false (by omega)]; l2eval))
    have hstep : stripTop (n + 1) i v = stripTop n i (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) := by
      simp only [stripTop, pow2_eq, Nat.add_assoc]
    rw [hstep]
    obtain ⟨m₄, hm₄, h₄⟩ := ih (by omega) (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))) (.pair (.pair (psub (.fst (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v)))) (ci 1)) (.snd (.fst (.pair (.pair (ci ((n + 1 : Nat) : Int)) (ci i)) (ci v))))) (ci (if v < 2 ^ (i + (n + 1)) then v else v - 2 ^ (i + (n + 1))))) (by l2eval) τ e₂ σ
    exact ⟨m₁ + m₂ + m₃ + m₄, by omega, (((h₁.trans (StepsN.letE h₂)).trans h₃).trans h₄)⟩

theorem bit_stepsN (b : Int) (i : Nat) (hi : i ≤ 7) (a : Atom₂) (ha : Atom.eval a = some (.pair (ci b) (ci i)))
    (τ : Ty₂) (e₂ : Tm₂) (σ : Store) :
    ∃ m ≤ 250, StepsN m (.letE τ (.app BITc a) e₂, σ) (e₂.subst 0 (ci (bitAt b i)), σ) := by
  obtain ⟨m₁, hm₁, h₁⟩ := stepsN_run 1 (c := (.letE τ (.app BITc a) e₂, σ))
    (d := (.letE τ (.letE tint (.app STRIPc (.pair (.pair (psub (ci 7) (.snd (.pair (ci b) (ci i)))) (.snd (.pair (ci b) (ci i)))) (.fst (.pair (ci b) (ci i))))) (.letE tint (.app POW (.snd (.pair (ci b) (ci i)))) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1))))) e₂, σ)) (by simp only [BITc]; l2eval)
  obtain ⟨m₂, hm₂, h₂⟩ := strip_stepsN (7 - i) i (by omega) b (.pair (.pair (psub (ci 7) (.snd (.pair (ci b) (ci i)))) (.snd (.pair (ci b) (ci i)))) (.fst (.pair (ci b) (ci i))))
    (by rw [show ((7 - i : Nat) : Int) = 7 - (i : Int) by omega]; l2eval) tint (.letE tint (.app POW (.snd (.pair (ci b) (ci i)))) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1)))) σ
  obtain ⟨m₃, hm₃, h₃⟩ := pow2_stepsN i (.snd (.pair (ci b) (ci i))) (by l2eval) tint (Tm.subst 1 (ci (stripTop (7 - i) i b)) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1)))) σ
  obtain ⟨m₄, hm₄, h₄⟩ := stepsN_run 2 (c := (.letE τ ((Tm.subst 1 (ci (stripTop (7 - i) i b)) (.ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1)))).subst 0 (ci (2 ^ i))) e₂, σ))
    (d := (e₂.subst 0 (ci (bitAt b i)), σ)) (by
      unfold bitAt
      rw [pow2_eq]
      by_cases h : stripTop (7 - i) i b < 2 ^ i
      · rw [if_pos h]; l2eval
      · rw [if_neg h]; l2eval
        all_goals (rw [show decide (stripTop (7 - i) i b < 2 ^ i) = false from decide_eq_false (by omega)]; l2eval))
  exact ⟨m₁ + m₂ + m₃ + m₄, by omega, (((h₁.trans (StepsN.letE h₂)).trans (StepsN.letE h₃)).trans h₄)⟩

theorem steps_via_bitN {c : Config} (k : Nat) {b : Int} {i : Nat} (hi : i ≤ 7) {K : Tm₂} {σ₁ : Store} {d : Config}
    {B : Nat} (h1 : run₂ k c = (.letE tint (.app BITc (.pair (ci b) (ci i))) K, σ₁))
    (h2 : ∃ m ≤ B, StepsN m (K.subst 0 (ci (bitAt b i)), σ₁) d) : ∃ m ≤ k + 250 + B, StepsN m c d := by
  obtain ⟨m₁, hm₁, s₁⟩ := stepsN_run k h1
  obtain ⟨m₂, hm₂, s₂⟩ := bit_stepsN b i hi (.pair (ci b) (ci i)) (by simp [Atom.eval]) tint K σ₁
  obtain ⟨m₃, hm₃, s₃⟩ := h2
  exact ⟨m₁ + m₂ + m₃, by omega, (s₁.trans s₂).trans s₃⟩

theorem table_stepN {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2068 ≤ L)
    (tb ti : Nat) (htb : f cTB = tb) (hti : f cTI = ti) (htb8 : tb < 256) (hti8 : ti ≤ 7) :
    ∃ m ≤ 2 + 250 + 10, StepsN m (closeAt p tableT, σ)
      (.ret (.const (.cap p)),
        if (tblNext tb ti).1 = 256 then ⟨(tblH σ.H p tb ti).insert (p + 0) 1, σ.R⟩ else ⟨tblH σ.H p tb ti, σ.R⟩) := by
  have hb := hw.cell 18 (by decide) (by omega)
  have hi := hw.cell 19 (by decide) (by omega)
  simp only [cTB, cTI] at htb hti
  apply steps_via_bitN 2 (B := 10) (b := (tb : Int)) hti8
  · conv_lhs => simp [closeAt, tableT, tableN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst,
      Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, hw.reg, hb, hi, htb, hti, Atom.eval, Atom.evalL,
      cTB, cTI, BITc_subst, show (18 : Int) < L by omega, show (19 : Int) < L by omega]
  · refine stepsN_le_run 10 (le_refl _) ?_
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

/-- **TABLE's step is a `stepS`.** -/
theorem stepS_table {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2068 ≤ L)
    (tb ti : Nat) (hmode : f cMODE = mTABLE) (htb : f cTB = tb) (hti : f cTI = ti) (htb8 : tb < 256) (hti8 : ti ≤ 7) :
    stepS p σ = some (if (tblNext tb ti).1 = 256 then ⟨(tblH σ.H p tb ti).insert (p + 0) 1, σ.R⟩
      else ⟨tblH σ.H p tb ti, σ.R⟩) := by
  obtain ⟨k₁, hk₁, h₁⟩ := step_dispatchN hw (by omega) mTABLE hmode
  have hl : modes.lookup mTABLE = some tableN := rfl
  rw [hl] at h₁
  obtain ⟨k₂, hk₂, h₂⟩ := table_stepN hw hL tb ti htb hti htb8 hti8
  have hrun := run₂_of_stepsN (h₁.trans h₂) rfl KSTEP (by simp only [KSTEP]; omega)
  unfold stepS
  rw [hrun]
  simp

/-- Worked instance of `stepS_of_mode` with `modes_fit`: HDR's one-step lemma is a `stepS`. -/
theorem stepS_hdr {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hm : f cMODE = mHDR) : stepS p σ = some ⟨reqH σ.H p 1 3, σ.R⟩ := by
  have hmem : (mHDR, hdrN) ∈ modes := by
    unfold modes; simp
  have hfit := modes_fit (mHDR, hdrN) hmem (by decide)
  exact stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (hdr_step hw hL)

end VIRDeflate.Step
