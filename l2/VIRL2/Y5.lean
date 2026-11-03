/-
  O95 layer L2, Lean arm. Y5 step 9 (STAGE-L2-LEAN): SEMANTIC TYPING, scored against errata L2-E1 + L2-E2 (an INDEX fault is
  permitted; nothing else). The triple `TripleIF` is `Triple` with "no reachable configuration FAULTS" weakened to "every
  reachable fault is an IndexFault". Y5 is proved SYNTACTICALLY: runtime typing is preserved along ⟶₂* (step 8) and every
  reachable configuration is terminal, steps, or index-faults (step 5). No fuel and no step index: `fix` is L1's unfolding
  step, typed by substitution.
  The postcondition says the program does not LEAK: a non-capability result leaves exactly `emp`; a capability result is
  ⟨p⟩ with exactly the one region at p. The OPEN form closes Γ ; Δ by a substitution (`Binds`): each available capability
  c ∈ Δ is bound to some ⟨p_c⟩ and the precondition owns region(p_c), ∗ over c; every other position gets a fitting value.
-/
import VIRL2.Preservation

namespace VIRL2
open VIRL1

theorem Store.union_empty (σ : Store) : σ ⊎ Store.empty = σ := by
  simp [Store.empty, Store.union, Finmap.union_empty]

/-- `{P} e {v. Q}` up to INDEX faults (errata L2-E1, L2-E2). -/
def TripleIF (P : Assn) (e : Tm₂) (Q : Atom₂ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    (∀ c, Steps₂ (e, σ ⊎ σf) c → ¬ (Faults c ∧ ¬ IndexFault c)) ∧
    (∀ a σ', Steps₂ (e, σ ⊎ σf) (.ret a, σ') →
      ∃ v σq, a.eval = some v ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v σq)

/-- Y5's postcondition at type τ: a typed value and `emp`, or (τ = cap) ⟨p⟩ and exactly the region at p. -/
def Y5Post (τ : Ty₂) : Atom₂ → Assn := fun v σ =>
  (τ ≠ tcap ∧ HasTypeA₂ [] v τ ∧ σ = Store.empty) ∨ (τ = tcap ∧ ∃ p n, v = .const (.cap p) ∧ IsRegion p n σ)

/-- Preservation along ⟶₂*. -/
theorem steps_rt : ∀ {c c' : Config}, Steps₂ c c' → ∀ {Ω τ σq σf}, RT [] [] Ω c.1 τ → OwnAll Ω σq →
    Store.Disj σq σf → Store.WF (σq ⊎ σf) → c.2 = σq ⊎ σf →
    ∃ Ω' σq', RT [] [] Ω' c'.1 τ ∧ OwnAll Ω' σq' ∧ Store.Disj σq' σf ∧ c'.2 = σq' ⊎ σf ∧ Store.WF (σq' ⊎ σf) := by
  intro c c' h
  induction h with
  | refl _ => intro Ω τ σq σf ht ho hd hwf hσ; exact ⟨Ω, σq, ht, ho, hd, hσ, hwf⟩
  | step h₁ _ ih =>
    intro Ω τ σq σf ht ho hd hwf hσ
    obtain ⟨Ω₁, σ₁, ht₁, ho₁, hd₁, hσ₁, hwf₁⟩ := pres_rt h₁ ht ho hd hwf hσ
    exact ih ht₁ ho₁ hd₁ (by rw [← hσ₁]; exact hwf₁) hσ₁

/-- Every owned region is live in the whole store. -/
theorem OwnAll.live {Ω : List Int} {p : Int} {σq : Store} (ho : OwnAll Ω σq) (hp : p ∈ Ω) (X : Store) :
    ∃ n, ((σq ⊎ X).R).lookup p = some n := by
  obtain ⟨σr, σs, -, rfl, ⟨n, hreg⟩, -⟩ := OwnAll.extract hp ho
  exact ⟨n, by rw [Store.union_assoc]; exact hreg.lookup_union _⟩

/-- The runtime form: a closed runtime-typed term owning Ω, from OwnAll Ω. -/
theorem rt_triple {Ω : List Int} {e : Tm₂} {τ : Ty₂} (ht : RT [] [] Ω e τ) : TripleIF (OwnAll Ω) e (Y5Post τ) := by
  intro σ σf ho hd hwf
  refine ⟨fun ⟨e', σc⟩ hc => ?_, fun a σ' hc => ?_⟩
  · obtain ⟨Ω', σq', ht', ho', -, hσ', hwf'⟩ := steps_rt hc ht ho hd hwf rfl
    dsimp only at ht' hσ'
    subst hσ'
    rintro ⟨⟨hnt, hns⟩, hnif⟩
    rcases progress_rt ht' hwf' (fun p hp => ho'.live hp σf) with h | ⟨c', hs⟩ | h
    · exact hnt h
    · exact hns c' hs
    · exact hnif h
  · obtain ⟨Ω', σq', ht', ho', hd', hσ', hwf'⟩ := steps_rt hc ht ho hd hwf rfl
    dsimp only at ht' hσ'
    subst hσ'
    cases ht' with
    | ret _ ha =>
      obtain ⟨v, hv, -, hvt⟩ := eval_total₂ _ ha
      refine ⟨v, σq', hv, hd', rfl, hwf', .inl ⟨?_, hvt, ho'⟩⟩
      have hn := atom_noCap ha
      rintro rfl; simp [hasCap, tcap] at hn
    | retCap hΓ _ => simp at hΓ
    | retCapC _ =>
      obtain ⟨σr, σe, -, rfl, ⟨n, hreg⟩, he⟩ := ho'
      have he' : σe = Store.empty := he
      subst he'
      refine ⟨.const (.cap _), σr ⊎ Store.empty, rfl, hd', rfl, hwf', .inr ⟨rfl, _, n, rfl, ?_⟩⟩
      rw [Store.union_empty]; exact hreg

/-- **Y5, CLOSED**: a closed well-typed L2 program, from `emp`, faults only out of bounds and leaks nothing. -/
theorem y5_closed {e : Tm₂} {τ : Ty₂} (h : HasType₂ [] [] e τ) : TripleIF Assn.emp e (Y5Post τ) :=
  rt_triple (RT.ofTyped h)

/-! ## The open form. -/

/-- Close an open term: substitute v₀ for index 0, then v₁ for the new index 0, … -/
def substAll : List Atom₂ → Tm₂ → Tm₂
  | [], e => e
  | v :: vs, e => substAll vs (e.subst 0 v)

/-- `Binds Γ Δ vs Ω`: vs closes Γ ; Δ, binding each AVAILABLE capability (Δ[n] = true) to a constant ⟨p⟩, the p's
  collected in Ω; every other position gets a value that fits its type. -/
inductive Binds : Ctx S₂ → List Bool → List Atom₂ → List Int → Prop where
  | nil : Binds [] [] [] []
  | val {Γ Δ vs Ω τ v} : Fits v τ → Binds Γ Δ vs Ω → Binds (τ :: Γ) (false :: Δ) (v :: vs) Ω
  | cap {Γ Δ vs Ω} (p : Int) : Binds Γ Δ vs Ω → Binds (tcap :: Γ) (true :: Δ) (.const (.cap p) :: vs) (p :: Ω)

theorem RT.substAll : ∀ {Γ Δ vs Ωc}, Binds Γ Δ vs Ωc → ∀ {Ω e τ}, RT Γ Δ Ω e τ →
    ∃ Ω', Ω'.Perm (Ωc ++ Ω) ∧ RT [] [] Ω' (substAll vs e) τ := by
  intro Γ Δ vs Ωc hb
  induction hb with
  | nil => intro Ω e τ ht; exact ⟨Ω, List.Perm.refl _, ht⟩
  | val hf _ ih => intro Ω e τ ht; exact ih (RT.substV (Γ₁ := []) (Δ₁ := []) rfl ht hf)
  | cap p _ ih =>
    intro Ω e τ ht
    obtain ⟨Ω', hp, ht'⟩ := ih (RT.substC (Γ₁ := []) (Δ₁ := []) p rfl ht)
    exact ⟨Ω', hp.trans List.perm_middle, ht'⟩

/-- **Y5, OPEN** (amend-16 Y5): `Γ ; Δ ⊢₂ e : τ` implies the triple with region(p_c) per c ∈ Δ (∗ over Δ), for every
  closing substitution; the program faults only out of bounds and leaks nothing. -/
theorem y5_open {Γ : Ctx S₂} {Δ : List Bool} {e : Tm₂} {τ : Ty₂} {vs : List Atom₂} {Ωc : List Int}
    (h : HasType₂ Γ Δ e τ) (hb : Binds Γ Δ vs Ωc) : TripleIF (OwnAll Ωc) (substAll vs e) (Y5Post τ) := by
  obtain ⟨Ω', hp, ht⟩ := RT.substAll hb (RT.ofTyped h)
  intro σ σf ho
  exact rt_triple ht σ σf (OwnAll.perm (by simpa using hp.symm) σ ho)

end VIRL2
