/-
  O95 layer L5, Lean arm (amend-24 LV4): SEMANTIC TYPING for L1′, proved as L2's Y5 was (DECLARATIONS-LEAN: syntactically, by
  preservation along ⟶₅* and progress, no fuel, no step index). The triple is L2's `TripleIF` over ⟶₅ with TWO terminal forms: a
  `ret a`, and a `retK a ds` that hands back capabilities. The postcondition says a well-typed program does not LEAK: a cap-free
  result hands back exactly the regions of its returned capabilities and owns nothing else; a capability result is ⟨p⟩ with
  exactly the one region at p.
-/
import VIRL5.Progress5
import VIRL2.Y5

namespace VIRL5
open VIRL1 VIRL2

/-- `{P} e {v, qs. Q}` up to INDEX faults (errata L2-E1, L2-E2 carried up), with both terminal forms. -/
def TripleIF₅ (P : Assn) (e : Tm₅) (Q : Atom₅ → List Atom₅ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    (∀ c, Steps₅ (e, σ ⊎ σf) c → ¬ (Faults₅ c ∧ ¬ IndexFault₅ c)) ∧
    (∀ a σ', Steps₅ (e, σ ⊎ σf) (.ret a, σ') →
      ∃ v σq, a.eval = some v ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v [] σq) ∧
    (∀ a ds σ', Steps₅ (e, σ ⊎ σf) (.retK a ds, σ') →
      ∃ v qs σq, a.eval = some v ∧ Atom₅.evalL ds = some qs ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v qs σq)

/-- The postcondition at (τ, k): a typed cap-free value with k handed-back constants, owning exactly their regions; or (τ = cap,
  k = 0) ⟨p⟩ with exactly the region at p. -/
def Y5Post₅ (τ : Ty₅) (k : Nat) : Atom₅ → List Atom₅ → Assn := fun v qs σ =>
  (τ ≠ t5cap ∧ HasTypeA₅ [] v τ ∧ ∃ ps, qs = capConsts ps ∧ ps.length = k ∧ OwnAll ps σ) ∨
  (τ = t5cap ∧ k = 0 ∧ qs = [] ∧ ∃ p n, v = .const (.cap p) ∧ IsRegion p n σ)

/-- Preservation along ⟶₅*. -/
theorem steps₅_rt : ∀ {c c' : Config₅}, Steps₅ c c' → ∀ {Ω τ k σq σf}, RT₅ [] [] Ω c.1 τ k → OwnAll Ω σq →
    Store.Disj σq σf → Store.WF (σq ⊎ σf) → c.2 = σq ⊎ σf →
    ∃ Ω' σq', RT₅ [] [] Ω' c'.1 τ k ∧ OwnAll Ω' σq' ∧ Store.Disj σq' σf ∧ c'.2 = σq' ⊎ σf ∧ Store.WF (σq' ⊎ σf) := by
  intro c c' h
  induction h with
  | refl _ => intro Ω τ k σq σf ht ho hd hwf hσ; exact ⟨Ω, σq, ht, ho, hd, hσ, hwf⟩
  | step h₁ _ ih =>
    intro Ω τ k σq σf ht ho hd hwf hσ
    obtain ⟨Ω₁, σ₁, ht₁, ho₁, hd₁, hσ₁, hwf₁⟩ := pres₅ h₁ ht ho hd hwf hσ
    exact ih ht₁ ho₁ hd₁ (by rw [← hσ₁]; exact hwf₁) hσ₁

theorem ne_t5cap_of {τ : Ty₅} (h : τ.hasCap = false) : τ ≠ t5cap := by
  rintro rfl; simp [Ty₅.hasCap, t5cap] at h

/-- The runtime form: a closed runtime-typed term owning Ω, from OwnAll Ω. -/
theorem rt_triple₅ {Ω : List Int} {e : Tm₅} {τ : Ty₅} {k : Nat} (ht : RT₅ [] [] Ω e τ k) :
    TripleIF₅ (OwnAll Ω) e (Y5Post₅ τ k) := by
  intro σ σf ho hd hwf
  refine ⟨fun ⟨e', σc⟩ hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · obtain ⟨Ω', σq', ht', ho', -, hσ', hwf'⟩ := steps₅_rt hc ht ho hd hwf rfl
    dsimp only at ht' hσ'
    subst hσ'
    rintro ⟨⟨hnt, hns⟩, hnif⟩
    rcases progress₅ ht' hwf' (fun p hp => ho'.live hp σf) with h | ⟨c', hs⟩ | h
    · exact hnt h
    · exact hns c' hs
    · exact hnif h
  · obtain ⟨Ω', σq', ht', ho', hd', hσ', hwf'⟩ := steps₅_rt hc ht ho hd hwf rfl
    dsimp only at ht' hσ'
    subst hσ'
    cases ht' with
    | ret _ ha =>
      obtain ⟨v, hv, -, hvt⟩ := eval_total₅ _ ha
      exact ⟨v, σq', hv, hd', rfl, hwf', .inl ⟨ne_t5cap_of (atom_noCap₅ ha), hvt, [], rfl, rfl, ho'⟩⟩
    | retCap hΓ _ => simp at hΓ
    | retCapC _ =>
      obtain ⟨σr, σe, -, rfl, ⟨n, hreg⟩, he⟩ := ho'
      have he' : σe = Store.empty := he
      subst he'
      refine ⟨.const (.cap _), σr ⊎ Store.empty, rfl, hd', rfl, hwf', .inr ⟨rfl, rfl, rfl, _, n, rfl, ?_⟩⟩
      rw [Store.union_empty]; exact hreg
  · obtain ⟨Ω', σq', ht', ho', hd', hσ', hwf'⟩ := steps₅_rt hc ht ho hd hwf rfl
    dsimp only at ht' hσ'
    subst hσ'
    obtain ⟨hk, hc', ha, hx⟩ := RT₅.retK_inv ht'
    obtain ⟨ps, rfl, hps⟩ := CapsRT.closed hx
    obtain ⟨v, hv, -, hvt⟩ := eval_total₅ _ ha
    exact ⟨v, capConsts ps, σq', hv, evalL_capConsts ps, hd', rfl, hwf',
      .inl ⟨ne_t5cap_of hc', hvt, ps, rfl, by rw [hk, capConsts_length], OwnAll.perm hps _ ho'⟩⟩

/-- **LV4's theorem, CLOSED**: a closed well-typed L1′ program, from `emp`, faults only out of bounds, and at its end owns exactly
  the regions it hands back (a cap-free result) or the one region of its capability result: it leaks nothing. -/
theorem y5_closed₅ {e : Tm₅} {τ : Ty₅} {k : Nat} (h : HasType₅ [] [] e τ k) : TripleIF₅ Assn.emp e (Y5Post₅ τ k) :=
  rt_triple₅ (RT₅.ofTyped h)

end VIRL5
