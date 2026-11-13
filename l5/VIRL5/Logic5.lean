/-
  O95 layer L5, Lean arm (amend-24 LV7 groundwork; DECLARATIONS-LEAN "the triple is L2's semantic Triple from ⟶₅"). The triple
  `{P} e {v, qs. Q}` over ⟶₅: from any σ ⊨ P beside any disjoint frame, no reachable configuration faults, and each terminal state
  (`ret a`, or `retK a ds` handing capabilities back) evaluates and leaves σ′ ⊎ σf with σ′ ⊨ Q v qs (qs = [] for `ret`). L2's
  structural rules restated: frame (every program, no side condition), consequence, ret, and a deterministic pure head step; the
  sequencing rules for `letE` (its head ends with nothing handed back) and `letK` (its head hands back exactly j).
-/
import VIRL5.Y5L5

namespace VIRL5
open VIRL1 VIRL2

def Triple₅ (P : Assn) (e : Tm₅) (Q : Atom₅ → List Atom₅ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    (∀ c, Steps₅ (e, σ ⊎ σf) c → ¬ Faults₅ c) ∧
    (∀ a σ', Steps₅ (e, σ ⊎ σf) (.ret a, σ') →
      ∃ v σq, a.eval = some v ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v [] σq) ∧
    (∀ a ds σ', Steps₅ (e, σ ⊎ σf) (.retK a ds, σ') →
      ∃ v qs σq, a.eval = some v ∧ Atom₅.evalL ds = some qs ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v qs σq)

/-- THE FRAME RULE over ⟶₅, for EVERY L1′ program: no side condition. -/
theorem frame₅ {P : Assn} {e : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} (R : Assn) (h : Triple₅ P e Q) :
    Triple₅ (P ∗ R) e (fun v qs => Q v qs ∗ R) := by
  intro σ σf hPR hd hwf
  obtain ⟨σp, σr, hpr, rfl, hP, hR⟩ := hPR
  have hd' : Store.Disj σp (σr ⊎ σf) := by
    rw [Store.disj_union_left] at hd
    exact (Store.disj_union_right _ _ _).2 ⟨hpr, hd.1⟩
  have hdr : Store.Disj σr σf := ((Store.disj_union_left _ _ _).1 hd).2
  rw [Store.union_assoc] at hwf ⊢
  obtain ⟨hsafe, hpost, hpostK⟩ := h σp (σr ⊎ σf) hP hd' hwf
  refine ⟨hsafe, fun a σ' hs => ?_, fun a ds σ' hs => ?_⟩
  · obtain ⟨v, σq, hv, hq, rfl, hw, hQ⟩ := hpost a σ' hs
    obtain ⟨hqr, hqf⟩ := (Store.disj_union_right _ _ _).1 hq
    exact ⟨v, σq ⊎ σr, hv, (Store.disj_union_left _ _ _).2 ⟨hqf, hdr⟩, (Store.union_assoc _ _ _).symm, hw,
      σq, σr, hqr, rfl, hQ, hR⟩
  · obtain ⟨v, qs, σq, hv, hqs, hq, rfl, hw, hQ⟩ := hpostK a ds σ' hs
    obtain ⟨hqr, hqf⟩ := (Store.disj_union_right _ _ _).1 hq
    exact ⟨v, qs, σq ⊎ σr, hv, hqs, (Store.disj_union_left _ _ _).2 ⟨hqf, hdr⟩, (Store.union_assoc _ _ _).symm, hw,
      σq, σr, hqr, rfl, hQ, hR⟩

theorem conseq₅ {P P' : Assn} {e : Tm₅} {Q Q' : Atom₅ → List Atom₅ → Assn} (hP : ∀ σ, P' σ → P σ)
    (hQ : ∀ v qs σ, Q v qs σ → Q' v qs σ) (h : Triple₅ P e Q) : Triple₅ P' e Q' := by
  intro σ σf hp hd hwf
  obtain ⟨hs, hpost, hpostK⟩ := h σ σf (hP σ hp) hd hwf
  refine ⟨hs, fun a σ' hst => ?_, fun a ds σ' hst => ?_⟩
  · obtain ⟨v, σq, hv, hq, he, hw, hQq⟩ := hpost a σ' hst
    exact ⟨v, σq, hv, hq, he, hw, hQ v [] σq hQq⟩
  · obtain ⟨v, qs, σq, hv, hqs, hq, he, hw, hQq⟩ := hpostK a ds σ' hst
    exact ⟨v, qs, σq, hv, hqs, hq, he, hw, hQ v qs σq hQq⟩

/-- Existential precondition. -/
theorem pre_ex₅ {α : Type} {P : α → Assn} {e : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} (h : ∀ x, Triple₅ (P x) e Q) :
    Triple₅ (fun σ => ∃ x, P x σ) e Q := by
  intro σ σf ⟨x, hx⟩ hd hwf; exact h x σ σf hx hd hwf

/-- A pure fact in the precondition. -/
theorem pre_pure₅ {φ : Prop} {P : Assn} {e : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} (h : φ → Triple₅ P e Q) :
    Triple₅ (fun σ => φ ∧ P σ) e Q := by
  intro σ σf ⟨hφ, hP⟩ hd hwf; exact h hφ σ σf hP hd hwf

/-! ## Terminal forms do not step. -/
theorem step₅_ret_none {a : Atom₅} {σ c} (h : Step₅ (Tm₅.ret a, σ) c) : False := by cases h
theorem step₅_retK_none {a : Atom₅} {ds σ c} (h : Step₅ (Tm₅.retK a ds, σ) c) : False := by cases h

theorem steps₅_ret {a : Atom₅} {σ c} (h : Steps₅ (Tm₅.ret a, σ) c) : c = (Tm₅.ret a, σ) := by
  cases h with
  | refl => rfl
  | step h₁ _ => exact (step₅_ret_none h₁).elim

theorem steps₅_retK {a : Atom₅} {ds σ c} (h : Steps₅ (Tm₅.retK a ds, σ) c) : c = (Tm₅.retK a ds, σ) := by
  cases h with
  | refl => rfl
  | step h₁ _ => exact (step₅_retK_none h₁).elim

theorem ret_rule₅ {a v : Atom₅} {Q : Atom₅ → List Atom₅ → Assn} (hv : a.eval = some v) : Triple₅ (Q v []) (.ret a) Q := by
  intro σ σf hQ hd hwf
  refine ⟨fun c hc => ?_, fun a' σ' hc => ?_, fun a' ds σ' hc => ?_⟩
  · rw [steps₅_ret hc]; exact fun hf => hf.1 trivial
  · have := steps₅_ret hc
    simp only [Prod.mk.injEq, Tm₅.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨v, σ, hv, hd, rfl, hwf, hQ⟩
  · have := steps₅_ret hc; simp at this

theorem retK_rule₅ {a v : Atom₅} {ds qs : List Atom₅} {Q : Atom₅ → List Atom₅ → Assn} (hv : a.eval = some v)
    (hqs : Atom₅.evalL ds = some qs) : Triple₅ (Q v qs) (.retK a ds) Q := by
  intro σ σf hQ hd hwf
  refine ⟨fun c hc => ?_, fun a' σ' hc => ?_, fun a' ds' σ' hc => ?_⟩
  · rw [steps₅_retK hc]; exact fun hf => hf.1 trivial
  · have := steps₅_retK hc; simp at this
  · have := steps₅_retK hc
    simp only [Prod.mk.injEq, Tm₅.retK.injEq] at this
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := this
    exact ⟨v, qs, σ, hv, hqs, hd, rfl, hwf, hQ⟩

theorem evalL_length : ∀ {ds qs : List Atom₅}, Atom₅.evalL ds = some qs → qs.length = ds.length
  | [], qs, h => by simp [Atom₅.evalL] at h; subst h; rfl
  | d :: ds, qs, h => by
      simp only [Atom₅.evalL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, -, qs', hqs', rfl⟩ := h
      simp [evalL_length hqs']

/-! ## letE. -/
theorem step₅_letE_inv {τ e₁ e₂ σ c'} (h : Step₅ (Tm₅.letE τ e₁ e₂, σ) c') :
    (∃ e₁' σ', Step₅ (e₁, σ) (e₁', σ') ∧ c' = (Tm₅.letE τ e₁' e₂, σ')) ∨
    (∃ a v, e₁ = .ret a ∧ Atom₅.eval a = some v ∧ c' = (e₂.subst 0 v, σ)) ∨
    (∃ a v, e₁ = .retK a [] ∧ Atom₅.eval a = some v ∧ c' = (e₂.subst 0 v, σ)) := by
  cases h with
  | letRet hv => exact .inr (.inl ⟨_, _, rfl, hv, rfl⟩)
  | letRetK0 hv => exact .inr (.inr ⟨_, _, rfl, hv, rfl⟩)
  | letStep hs => exact .inl ⟨_, _, hs, rfl⟩

theorem steps₅_letE {τ e₁ e₂ σ c} (h : Steps₅ (Tm₅.letE τ e₁ e₂, σ) c) :
    (∃ e₁' σ', Steps₅ (e₁, σ) (e₁', σ') ∧ c = (Tm₅.letE τ e₁' e₂, σ')) ∨
    (∃ a v σ', Steps₅ (e₁, σ) (.ret a, σ') ∧ Atom₅.eval a = some v ∧ Steps₅ (e₂.subst 0 v, σ') c) ∨
    (∃ a v σ', Steps₅ (e₁, σ) (.retK a [], σ') ∧ Atom₅.eval a = some v ∧ Steps₅ (e₂.subst 0 v, σ') c) := by
  generalize hc₀ : (Tm₅.letE τ e₁ e₂, σ) = c₀ at h
  induction h generalizing e₁ σ with
  | refl => subst hc₀; exact .inl ⟨e₁, σ, .refl _, rfl⟩
  | step h₁ h₂ ih =>
    subst hc₀
    rcases step₅_letE_inv h₁ with ⟨e₁', σ', hs, rfl⟩ | ⟨a, v, rfl, hv, rfl⟩ | ⟨a, v, rfl, hv, rfl⟩
    · rcases ih rfl with ⟨e₁'', σ'', hs', rfl⟩ | ⟨a, v, σ'', hs', hv, hc⟩ | ⟨a, v, σ'', hs', hv, hc⟩
      · exact .inl ⟨e₁'', σ'', .step hs hs', rfl⟩
      · exact .inr (.inl ⟨a, v, σ'', .step hs hs', hv, hc⟩)
      · exact .inr (.inr ⟨a, v, σ'', .step hs hs', hv, hc⟩)
    · exact .inr (.inl ⟨a, v, σ, .refl _, hv, h₂⟩)
    · exact .inr (.inr ⟨a, v, σ, .refl _, hv, h₂⟩)

/-- The `let x:τ = e₁ in e₂` rule: the head hands nothing back (`hQ`). -/
theorem letE_rule₅ {P : Assn} {τ : Ty₅} {e₁ e₂ : Tm₅} {Q R : Atom₅ → List Atom₅ → Assn} (h₁ : Triple₅ P e₁ Q)
    (hQ : ∀ v qs σ, Q v qs σ → qs = []) (h₂ : ∀ v, Triple₅ (Q v []) (e₂.subst 0 v) R) : Triple₅ P (.letE τ e₁ e₂) R := by
  intro σ σf hP hd hwf
  obtain ⟨hs₁, hp₁, hk₁⟩ := h₁ σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · rcases steps₅_letE hc with ⟨e₁', σ', hs, rfl⟩ | ⟨a, v, σ', hs, hv, hc'⟩ | ⟨a, v, σ', hs, hv, hc'⟩
    · rintro ⟨-, hns⟩
      cases e₁' with
      | ret a =>
        obtain ⟨v, -, hv, -⟩ := hp₁ a σ' hs
        exact hns _ (.letRet hv)
      | retK a ds =>
        obtain ⟨v, qs, σq, hv, hqs, -, -, -, hQq⟩ := hk₁ a ds σ' hs
        obtain rfl := hQ _ _ _ hQq
        cases ds with
        | nil => exact hns _ (.letRetK0 hv)
        | cons _ _ => have := evalL_length hqs; simp at this
      | _ =>
        have hnf := hs₁ _ hs
        apply hnf
        refine ⟨fun h => h, fun ⟨e'', σ''⟩ hst => hns _ (.letStep hst)⟩
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a σ' hs
      rw [hv] at hv'; cases hv'
      exact (h₂ v σq σf hQq hdq hwq).1 c hc'
    · obtain ⟨v', qs, σq, hv', hqs, hdq, rfl, hwq, hQq⟩ := hk₁ a [] σ' hs
      rw [hv] at hv'; cases hv'
      simp [Atom₅.evalL] at hqs; subst hqs
      exact (h₂ v σq σf hQq hdq hwq).1 c hc'
  · rcases steps₅_letE hc with ⟨e₁', σ'', hs, heq⟩ | ⟨a', v, σ'', hs, hv, hc'⟩ | ⟨a', v, σ'', hs, hv, hc'⟩
    · simp at heq
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a' σ'' hs
      rw [hv] at hv'; cases hv'
      exact (h₂ v σq σf hQq hdq hwq).2.1 a σ' hc'
    · obtain ⟨v', qs, σq, hv', hqs, hdq, rfl, hwq, hQq⟩ := hk₁ a' [] σ'' hs
      rw [hv] at hv'; cases hv'
      simp [Atom₅.evalL] at hqs; subst hqs
      exact (h₂ v σq σf hQq hdq hwq).2.1 a σ' hc'
  · rcases steps₅_letE hc with ⟨e₁', σ'', hs, heq⟩ | ⟨a', v, σ'', hs, hv, hc'⟩ | ⟨a', v, σ'', hs, hv, hc'⟩
    · simp at heq
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a' σ'' hs
      rw [hv] at hv'; cases hv'
      exact (h₂ v σq σf hQq hdq hwq).2.2 a ds σ' hc'
    · obtain ⟨v', qs, σq, hv', hqs, hdq, rfl, hwq, hQq⟩ := hk₁ a' [] σ'' hs
      rw [hv] at hv'; cases hv'
      simp [Atom₅.evalL] at hqs; subst hqs
      exact (h₂ v σq σf hQq hdq hwq).2.2 a ds σ' hc'

/-! ## letK. -/
theorem step₅_letK_inv {τ j e₁ e₂ σ c'} (h : Step₅ (Tm₅.letK τ j e₁ e₂, σ) c') :
    (∃ e₁' σ', Step₅ (e₁, σ) (e₁', σ') ∧ c' = (Tm₅.letK τ j e₁' e₂, σ')) ∨
    (∃ a ds v qs, e₁ = .retK a ds ∧ Atom₅.eval a = some v ∧ Atom₅.evalL ds = some qs ∧ qs.length = j ∧
      c' = (Tm₅.substAll (v :: qs) e₂, σ)) ∨
    (∃ a v, j = 0 ∧ e₁ = .ret a ∧ Atom₅.eval a = some v ∧ c' = (e₂.subst 0 v, σ)) := by
  cases h with
  | letKRet hv hqs hl => exact .inr (.inl ⟨_, _, _, _, rfl, hv, hqs, hl, rfl⟩)
  | letKRet0 hv => exact .inr (.inr ⟨_, _, rfl, rfl, hv, rfl⟩)
  | letKStep hs => exact .inl ⟨_, _, hs, rfl⟩

theorem steps₅_letK {τ j e₁ e₂ σ c} (h : Steps₅ (Tm₅.letK τ j e₁ e₂, σ) c) :
    (∃ e₁' σ', Steps₅ (e₁, σ) (e₁', σ') ∧ c = (Tm₅.letK τ j e₁' e₂, σ')) ∨
    (∃ a ds v qs σ', Steps₅ (e₁, σ) (.retK a ds, σ') ∧ Atom₅.eval a = some v ∧ Atom₅.evalL ds = some qs ∧
      qs.length = j ∧ Steps₅ (Tm₅.substAll (v :: qs) e₂, σ') c) ∨
    (∃ a v σ', j = 0 ∧ Steps₅ (e₁, σ) (.ret a, σ') ∧ Atom₅.eval a = some v ∧ Steps₅ (e₂.subst 0 v, σ') c) := by
  generalize hc₀ : (Tm₅.letK τ j e₁ e₂, σ) = c₀ at h
  induction h generalizing e₁ σ with
  | refl => subst hc₀; exact .inl ⟨e₁, σ, .refl _, rfl⟩
  | step h₁ h₂ ih =>
    subst hc₀
    rcases step₅_letK_inv h₁ with ⟨e₁', σ', hs, rfl⟩ | ⟨a, ds, v, qs, rfl, hv, hqs, hl, rfl⟩ | ⟨a, v, hj, rfl, hv, rfl⟩
    · rcases ih rfl with ⟨e₁'', σ'', hs', rfl⟩ | ⟨a, ds, v, qs, σ'', hs', hv, hqs, hl, hc⟩ | ⟨a, v, σ'', hj, hs', hv, hc⟩
      · exact .inl ⟨e₁'', σ'', .step hs hs', rfl⟩
      · exact .inr (.inl ⟨a, ds, v, qs, σ'', .step hs hs', hv, hqs, hl, hc⟩)
      · exact .inr (.inr ⟨a, v, σ'', hj, .step hs hs', hv, hc⟩)
    · exact .inr (.inl ⟨a, ds, v, qs, σ, .refl _, hv, hqs, hl, h₂⟩)
    · exact .inr (.inr ⟨a, v, σ, hj, .refl _, hv, h₂⟩)

/-- The `let x:τ, c₁′ … c_j′ ⇐ e₁ in e₂` rule: every terminal state of the head hands back exactly j values (`hQ`). -/
theorem letK_rule₅ {P : Assn} {τ : Ty₅} {j : Nat} {e₁ e₂ : Tm₅} {Q R : Atom₅ → List Atom₅ → Assn} (h₁ : Triple₅ P e₁ Q)
    (hQ : ∀ v qs σ, Q v qs σ → qs.length = j)
    (h₂ : ∀ v qs, qs.length = j → Triple₅ (Q v qs) (Tm₅.substAll (v :: qs) e₂) R) : Triple₅ P (.letK τ j e₁ e₂) R := by
  intro σ σf hP hd hwf
  obtain ⟨hs₁, hp₁, hk₁⟩ := h₁ σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · rcases steps₅_letK hc with ⟨e₁', σ', hs, rfl⟩ | ⟨a, ds, v, qs, σ', hs, hv, hqs, hl, hc'⟩ | ⟨a, v, σ', hj, hs, hv, hc'⟩
    · rintro ⟨-, hns⟩
      cases e₁' with
      | ret a =>
        obtain ⟨v, σq, hv, -, -, -, hQq⟩ := hp₁ a σ' hs
        have hj := hQ _ _ _ hQq; simp at hj; subst hj
        exact hns _ (.letKRet0 hv)
      | retK a ds =>
        obtain ⟨v, qs, σq, hv, hqs, -, -, -, hQq⟩ := hk₁ a ds σ' hs
        exact hns _ (.letKRet hv hqs (hQ _ _ _ hQq))
      | _ =>
        have hnf := hs₁ _ hs
        apply hnf
        refine ⟨fun h => h, fun ⟨e'', σ''⟩ hst => hns _ (.letKStep hst)⟩
    · obtain ⟨v', qs', σq, hv', hqs', hdq, rfl, hwq, hQq⟩ := hk₁ a ds σ' hs
      rw [hv] at hv'; cases hv'; rw [hqs] at hqs'; cases hqs'
      exact (h₂ v qs hl σq σf hQq hdq hwq).1 c hc'
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a σ' hs
      rw [hv] at hv'; cases hv'
      subst hj
      exact (h₂ v [] rfl σq σf hQq hdq hwq).1 c hc'
  · rcases steps₅_letK hc with ⟨e₁', σ'', hs, heq⟩ | ⟨a', ds, v, qs, σ'', hs, hv, hqs, hl, hc'⟩ | ⟨a', v, σ'', hj, hs, hv, hc'⟩
    · simp at heq
    · obtain ⟨v', qs', σq, hv', hqs', hdq, rfl, hwq, hQq⟩ := hk₁ a' ds σ'' hs
      rw [hv] at hv'; cases hv'; rw [hqs] at hqs'; cases hqs'
      exact (h₂ v qs hl σq σf hQq hdq hwq).2.1 a σ' hc'
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a' σ'' hs
      rw [hv] at hv'; cases hv'
      subst hj
      exact (h₂ v [] rfl σq σf hQq hdq hwq).2.1 a σ' hc'
  · rcases steps₅_letK hc with ⟨e₁', σ'', hs, heq⟩ | ⟨a', ds', v, qs, σ'', hs, hv, hqs, hl, hc'⟩ | ⟨a', v, σ'', hj, hs, hv, hc'⟩
    · simp at heq
    · obtain ⟨v', qs', σq, hv', hqs', hdq, rfl, hwq, hQq⟩ := hk₁ a' ds' σ'' hs
      rw [hv] at hv'; cases hv'; rw [hqs] at hqs'; cases hqs'
      exact (h₂ v qs hl σq σf hQq hdq hwq).2.2 a ds σ' hc'
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQq⟩ := hp₁ a' σ'' hs
      rw [hv] at hv'; cases hv'
      subst hj
      exact (h₂ v [] rfl σq σf hQq hdq hwq).2.2 a ds σ' hc'

/-- A deterministic head step that leaves the store alone: e inherits e′'s triple. -/
theorem pure_step_rule₅ {P : Assn} {e e' : Tm₅} {Q : Atom₅ → List Atom₅ → Assn}
    (hstep : ∀ σ, Step₅ (e, σ) (e', σ)) (hdet : ∀ σ c, Step₅ (e, σ) c → c = (e', σ)) (h : Triple₅ P e' Q) :
    Triple₅ P e Q := by
  intro σ σf hP hd hwf
  obtain ⟨hs, hp, hk⟩ := h σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · cases hc with
    | refl => exact fun hf => hf.2 _ (hstep _)
    | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact hs c h₂
  · cases hc with
    | refl => cases hstep (σ ⊎ σf)
    | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact hp a σ' h₂
  · cases hc with
    | refl => cases hstep (σ ⊎ σf)
    | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact hk a ds σ' h₂

end VIRL5
