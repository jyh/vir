/-
  O95 layer L5, Lean arm (DECLARATIONS-LEAN Addendum 5; LV8-MAP.md infrastructure 2): the COST clause. `Cost₅ P e n`: from every
  framed P-store, `run₅ n` reaches a terminal configuration. With ⟶₅ deterministic (Run5.lean), that bounds the run. The
  composition rules mirror the triple's (Logic5/Ops5) and add one step per head. A routine's cost is a SECOND lemma proved with
  the routine, never by a client unfolding its body (LV8).
-/
import VIRL5.Run5
import VIRL5.Ops5

namespace VIRL5
open VIRL1 VIRL2

/-! ## Counted ⟶₅ and `run₅` -/

inductive StepsN₅ : Nat → Config₅ → Config₅ → Prop where
  | refl (c : Config₅) : StepsN₅ 0 c c
  | step {n : Nat} {c c' c'' : Config₅} : Step₅ c c' → StepsN₅ n c' c'' → StepsN₅ (n + 1) c c''

theorem StepsN₅.trans {a b : Nat} {c₁ c₂ c₃ : Config₅} (h₁ : StepsN₅ a c₁ c₂) (h₂ : StepsN₅ b c₂ c₃) :
    StepsN₅ (a + b) c₁ c₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | @step n c c' c'' s _ ih => rw [show n + 1 + b = (n + b) + 1 by omega]; exact .step s (ih h₂)

theorem StepsN₅.steps {n : Nat} {c d : Config₅} (h : StepsN₅ n c d) : Steps₅ c d := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step s ih

theorem StepsN₅.letE {n : Nat} {τ : Ty₅} {e₁ e₁' e₂ : Tm₅} {σ σ' : Store} (h : StepsN₅ n (e₁, σ) (e₁', σ')) :
    StepsN₅ n (.letE τ e₁ e₂, σ) (.letE τ e₁' e₂, σ') := by
  generalize hc : (e₁, σ) = c at h
  generalize hd : (e₁', σ') = d at h
  induction h generalizing e₁ σ with
  | refl => subst hc; cases hd; exact .refl _
  | @step n c c' c'' s _ ih =>
    subst hc
    obtain ⟨e₂', σ₂⟩ := c'
    exact .step (.letStep s) (ih rfl hd)

theorem StepsN₅.letK {n : Nat} {τ : Ty₅} {j : Nat} {e₁ e₁' e₂ : Tm₅} {σ σ' : Store} (h : StepsN₅ n (e₁, σ) (e₁', σ')) :
    StepsN₅ n (.letK τ j e₁ e₂, σ) (.letK τ j e₁' e₂, σ') := by
  generalize hc : (e₁, σ) = c at h
  generalize hd : (e₁', σ') = d at h
  induction h generalizing e₁ σ with
  | refl => subst hc; cases hd; exact .refl _
  | @step n c c' c'' s _ ih =>
    subst hc
    obtain ⟨e₂', σ₂⟩ := c'
    exact .step (.letKStep s) (ih rfl hd)

theorem run₅_stuck {c : Config₅} (h : stepFn₅ c.1 c.2 = none) : ∀ n, run₅ n c = c
  | 0 => rfl
  | n + 1 => by simp [run₅, h]

theorem run₅_terminal {c : Config₅} (h : c.1.IsTerminal) (n : Nat) : run₅ n c = c := by
  apply run₅_stuck
  obtain ⟨e, σ⟩ := c
  cases e <;> simp_all [Tm₅.IsTerminal, stepFn₅_ret, stepFn₅_retK]

theorem run₅_add : ∀ (a b : Nat) (c : Config₅), run₅ (a + b) c = run₅ b (run₅ a c)
  | 0, b, c => by simp [run₅]
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [run₅]
    split
    · rename_i c' _; exact run₅_add a b c'
    · rename_i h; exact (run₅_stuck h b).symm

theorem run₅_of_stepsN {n : Nat} {c d : Config₅} (h : StepsN₅ n c d) (m : Nat) : run₅ (n + m) c = run₅ m d := by
  induction h with
  | refl => simp
  | @step n c c' c'' s _ ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [run₅, stepFn₅_complete s]
    exact ih

theorem stepsN_of_run₅ : ∀ (n : Nat) (c : Config₅), ∃ k ≤ n, StepsN₅ k c (run₅ n c)
  | 0, c => ⟨0, le_refl _, .refl c⟩
  | n + 1, c => by
    simp only [run₅]
    split
    · rename_i c' h
      obtain ⟨k, hk, hs⟩ := stepsN_of_run₅ n c'
      exact ⟨k + 1, by omega, .step (stepFn₅_sound h) hs⟩
    · exact ⟨0, by omega, .refl c⟩

theorem run₅_mono {n m : Nat} {c : Config₅} (h : (run₅ n c).1.IsTerminal) (hnm : n ≤ m) : run₅ m c = run₅ n c := by
  rw [show m = n + (m - n) by omega, run₅_add, run₅_terminal h]

/-! ## The cost clause and its rules -/

def Cost₅ (P : Assn) (e : Tm₅) (n : Nat) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) → (run₅ n (e, σ ⊎ σf)).1.IsTerminal

theorem Cost₅.mono {P : Assn} {e : Tm₅} {n m : Nat} (h : Cost₅ P e n) (hnm : n ≤ m) : Cost₅ P e m := by
  intro σ σf hP hd hwf
  rw [run₅_mono (h σ σf hP hd hwf) hnm]
  exact h σ σf hP hd hwf

theorem cost_conseq₅ {P P' : Assn} {e : Tm₅} {n : Nat} (hP : ∀ σ, P' σ → P σ) (h : Cost₅ P e n) : Cost₅ P' e n :=
  fun σ σf hp hd hwf => h σ σf (hP σ hp) hd hwf

theorem cost_pre_pure₅ {φ : Prop} {P : Assn} {e : Tm₅} {n : Nat} (h : φ → Cost₅ P e n) :
    Cost₅ (fun σ => φ ∧ P σ) e n :=
  fun σ σf ⟨hφ, hP⟩ hd hwf => h hφ σ σf hP hd hwf

theorem cost_ret₅ (P : Assn) (a : Atom₅) : Cost₅ P (.ret a) 0 := fun _ _ _ _ _ => trivial
theorem cost_retK₅ (P : Assn) (a : Atom₅) (ds : List Atom₅) : Cost₅ P (.retK a ds) 0 := fun _ _ _ _ _ => trivial

/-- A head step that leaves the store alone costs one. -/
theorem cost_pure_step₅ {P : Assn} {e e' : Tm₅} {n : Nat} (hstep : ∀ σ, Step₅ (e, σ) (e', σ)) (h : Cost₅ P e' n) :
    Cost₅ P e (n + 1) := by
  intro σ σf hP hd hwf
  have := run₅_of_stepsN (.step (hstep (σ ⊎ σf)) (.refl _)) n
  rw [show 1 + n = n + 1 by omega] at this
  rw [this]
  exact h σ σf hP hd hwf

/-- The converse: e′ costs one less than e when e steps to e′ without touching the store (⟶₅ is deterministic). -/
theorem cost_pure_step_rev₅ {P : Assn} {e e' : Tm₅} {n : Nat} (hstep : ∀ σ, Step₅ (e, σ) (e', σ)) (h : Cost₅ P e (n + 1)) :
    Cost₅ P e' n := by
  intro σ σf hP hd hwf
  have := h σ σf hP hd hwf
  simp only [run₅, stepFn₅_complete (hstep (σ ⊎ σf))] at this
  exact this

theorem cost_ite₅ {P : Assn} {a : Atom₅} {e₁ e₂ : Tm₅} {b : Bool} {n : Nat}
    (ha : a.eval = some (.const (.bool b))) (h : Cost₅ P (if b then e₁ else e₂) n) : Cost₅ P (.ite a e₁ e₂) (n + 1) := by
  refine cost_pure_step₅ (fun σ => ?_) h
  cases b
  · exact .iteF ha rfl
  · exact .iteT ha rfl

theorem cost_appKFix₅ {P : Assn} {a₁ a₂ : Atom₅} {cs qs : List Atom₅} {τ₁ τ₂ : Ty₅} {k : Nat} {e : Tm₅} {v : Atom₅} {n : Nat}
    (h₁ : a₁.eval = some (.fix τ₁ k τ₂ e)) (h₂ : a₂.eval = some v) (hqs : Atom₅.evalL cs = some qs) (hl : qs.length = k)
    (h : Cost₅ P (Tm₅.substAll (.fix τ₁ k τ₂ e :: v :: qs) e) n) : Cost₅ P (.appK a₁ a₂ cs) (n + 1) :=
  cost_pure_step₅ (fun _ => .appKFix h₁ h₂ hqs hl) h

theorem cost_appFix₅ {P : Assn} {a₁ a₂ : Atom₅} {τ₁ τ₂ : Ty₅} {e : Tm₅} {v : Atom₅} {n : Nat}
    (h₁ : a₁.eval = some (.fix τ₁ 0 τ₂ e)) (h₂ : a₂.eval = some v)
    (h : Cost₅ P ((e.subst 0 v).subst 0 (.fix τ₁ 0 τ₂ e)) n) : Cost₅ P (.app a₁ a₂) (n + 1) :=
  cost_pure_step₅ (fun _ => .appFix h₁ h₂) h

/-- `let x ← o(a⃗) in e`: one step for the operation, then the body at the operation's post. -/
theorem cost_letOp₅ {P : Assn} {o : Op} {as : List Atom₅} {τ : Ty₅} {e : Tm₅} {cs : List Const} {Q : Atom₂ → Assn} {n : Nat}
    (hvs : Atom₅.evalL as = some (cs.map Atom₅.const)) (ho : OpTriple P o (cs.map Atom.const) Q)
    (hk : ∀ v, Cost₅ (Q v) (e.subst 0 (ιA v)) n) : Cost₅ P (.letOp o as τ e) (n + 1) := by
  intro σ σf hP hd hwf
  obtain ⟨v, σq, hop, hdq, hwfq, hQ⟩ := ho σ σf hP hd hwf
  have := run₅_of_stepsN (.step (Step₅.op (τ := τ) (e := e) hvs (op5_of hop)) (.refl _)) n
  rw [show 1 + n = n + 1 by omega] at this
  rw [this]
  exact hk v σq σf hQ hdq hwfq

/-- `let x = e₁ in e₂`: the head's cost, one step to bind, the body's cost at the head's post. -/
theorem cost_letE₅ {P : Assn} {τ : Ty₅} {e₁ e₂ : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} {n₁ n₂ : Nat}
    (h₁ : Triple₅ P e₁ Q) (c₁ : Cost₅ P e₁ n₁) (hQ : ∀ v qs σ, Q v qs σ → qs = [])
    (c₂ : ∀ v, Cost₅ (Q v []) (e₂.subst 0 v) n₂) : Cost₅ P (.letE τ e₁ e₂) (n₁ + 1 + n₂) := by
  intro σ σf hP hd hwf
  have hterm := c₁ σ σf hP hd hwf
  obtain ⟨k, hk, hsN⟩ := stepsN_of_run₅ n₁ (e₁, σ ⊎ σf)
  obtain ⟨_, hpost, hpostK⟩ := h₁ σ σf hP hd hwf
  generalize ht : run₅ n₁ (e₁, σ ⊎ σf) = t at hterm hsN
  obtain ⟨t₁, s'⟩ := t
  have hlet := StepsN₅.letE (τ := τ) (e₂ := e₂) hsN
  cases t₁ with
  | ret a =>
    obtain ⟨v, σq, hv, hdq, rfl, hwq, hQq⟩ := hpost a _ hsN.steps
    have hall := hlet.trans (.step (.letRet hv) (.refl _))
    have hc := c₂ v σq σf hQq hdq hwq
    have hr := run₅_of_stepsN hall n₂
    rw [← hr] at hc
    rw [run₅_mono hc (by omega : k + 1 + n₂ ≤ n₁ + 1 + n₂)]
    exact hc
  | retK a ds =>
    obtain ⟨v, qs, σq, hv, hqs, hdq, rfl, hwq, hQq⟩ := hpostK a ds _ hsN.steps
    obtain rfl := hQ _ _ _ hQq
    cases ds with
    | cons _ _ => have := evalL_length hqs; simp at this
    | nil =>
      have hall := hlet.trans (.step (.letRetK0 hv) (.refl _))
      have hc := c₂ v σq σf hQq hdq hwq
      have hr := run₅_of_stepsN hall n₂
      rw [← hr] at hc
      rw [run₅_mono hc (by omega : k + 1 + n₂ ≤ n₁ + 1 + n₂)]
      exact hc
  | _ => simp [Tm₅.IsTerminal] at hterm

/-- `let x, c′… ⇐ e₁ in e₂` (j handed back): the head's cost, one step to bind, the body's cost at the head's post. -/
theorem cost_letK₅ {P : Assn} {τ : Ty₅} {j : Nat} {e₁ e₂ : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} {n₁ n₂ : Nat}
    (h₁ : Triple₅ P e₁ Q) (c₁ : Cost₅ P e₁ n₁) (hQ : ∀ v qs σ, Q v qs σ → qs.length = j)
    (c₂ : ∀ v qs, qs.length = j → Cost₅ (Q v qs) (Tm₅.substAll (v :: qs) e₂) n₂) :
    Cost₅ P (.letK τ j e₁ e₂) (n₁ + 1 + n₂) := by
  intro σ σf hP hd hwf
  have hterm := c₁ σ σf hP hd hwf
  obtain ⟨k, hk, hsN⟩ := stepsN_of_run₅ n₁ (e₁, σ ⊎ σf)
  obtain ⟨_, hpost, hpostK⟩ := h₁ σ σf hP hd hwf
  generalize ht : run₅ n₁ (e₁, σ ⊎ σf) = t at hterm hsN
  obtain ⟨t₁, s'⟩ := t
  have hlet := StepsN₅.letK (τ := τ) (j := j) (e₂ := e₂) hsN
  cases t₁ with
  | ret a =>
    obtain ⟨v, σq, hv, hdq, rfl, hwq, hQq⟩ := hpost a _ hsN.steps
    have hj := hQ _ _ _ hQq
    simp at hj
    subst hj
    have hall := hlet.trans (.step (.letKRet0 hv) (.refl _))
    have hc := c₂ v [] rfl σq σf hQq hdq hwq
    have hr := run₅_of_stepsN hall n₂
    simp only [Tm₅.substAll] at hc
    rw [← hr] at hc
    rw [run₅_mono hc (by omega : k + 1 + n₂ ≤ n₁ + 1 + n₂)]
    exact hc
  | retK a ds =>
    obtain ⟨v, qs, σq, hv, hqs, hdq, rfl, hwq, hQq⟩ := hpostK a ds _ hsN.steps
    have hj := hQ _ _ _ hQq
    have hall := hlet.trans (.step (.letKRet hv hqs hj) (.refl _))
    have hc := c₂ v qs hj σq σf hQq hdq hwq
    have hr := run₅_of_stepsN hall n₂
    rw [← hr] at hc
    rw [run₅_mono hc (by omega : k + 1 + n₂ ≤ n₁ + 1 + n₂)]
    exact hc
  | _ => simp [Tm₅.IsTerminal] at hterm

end VIRL5
