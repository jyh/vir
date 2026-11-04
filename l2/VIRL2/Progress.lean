/-
  O95 layer L2, Lean arm. Y5, PROGRESS: a closed runtime-typed configuration whose owned regions are live, in a well-formed
  store, is terminal, or steps, or is an INDEX fault (errata L2-E1, L2-E2). No other fault is possible.
-/
import VIRL2.Runtime

namespace VIRL2
open VIRL1

theorem canon_int {v : Atom₂} (hv : v.IsValue) (h : HasTypeA₂ [] v tint) : ∃ k, v = .const (.int k) := by
  obtain ⟨c, rfl, hc, -⟩ := canon_base₂ hv h
  cases c <;> simp [Const.ty] at hc; exact ⟨_, rfl⟩

theorem canon_bool {v : Atom₂} (hv : v.IsValue) (h : HasTypeA₂ [] v tbool) : ∃ b, v = .const (.bool b) := by
  obtain ⟨c, rfl, hc, -⟩ := canon_base₂ hv h
  cases c <;> simp [Const.ty] at hc; exact ⟨_, rfl⟩

theorem progress_rt : ∀ {Δ Ω e τ} {σ : Store}, RT [] Δ Ω e τ → Store.WF σ → (∀ p ∈ Ω, ∃ n, σ.R.lookup p = some n) →
    e.IsTerminal ∨ (∃ c, Step₂ (e, σ) c) ∨ IndexFault (e, σ)
  | _, _, _, _, _, .ret _ _, _, _ => .inl trivial
  | _, _, _, _, _, .retCap hΓ _, _, _ => by simp at hΓ
  | _, _, _, _, _, .retCapC _, _, _ => .inl trivial
  | _, _, _, _, σ, .letE (e₁ := e₁) _ hp _ h₁ _, hwf, hown => by
    have hown₁ : ∀ p ∈ _, ∃ n, σ.R.lookup p = some n := fun p hp' => hown p (hp.symm.subset (List.mem_append_left _ hp'))
    rcases progress_rt h₁ hwf hown₁ with ht | ⟨⟨e₁', σ'⟩, hs⟩ | hf
    · cases e₁ with
      | ret a =>
        right; left
        cases h₁ with
        | ret _ ha =>
          obtain ⟨v, hv, -, -⟩ := eval_total₂ a ha
          exact ⟨_, .pure (.letRet hv)⟩
        | retCap hΓ _ => simp at hΓ
        | retCapC _ => exact ⟨_, .pure (.letRet rfl)⟩
      | _ => exact ht.elim
    · exact .inr (.inl ⟨_, .letStep hs⟩)
    · exact .inr (.inr (.letE hf))
  | _, _, _, _, σ, .alloc (a := a) ha _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₂ a ha
    obtain ⟨k, rfl⟩ := canon_int hval hvt
    by_cases hk : 0 < k
    · right; left
      have hs : (opStep .alloc [.const (.int k)] σ).isSome := by simp [opStep, Store.alloc, hk]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom.evalL, hv]) hop⟩
    · exact .inr (.inr (.alloc hv (by omega)))
  | _, _, _, _, _, .load hΓ _ _ _, _, _ => by simp at hΓ
  | _, _, _, _, σ, .loadC (p := p) (a := a) hp ha _, hwf, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₂ a ha
    obtain ⟨i, rfl⟩ := canon_int hval hvt
    by_cases hi : 0 ≤ i ∧ i < n
    · have hmem : p + i ∈ σ.H := (hwf.domH _).2 ⟨p, n, hn, by unfold Store.InRegion; omega⟩
      obtain ⟨w, hw⟩ := Finmap.mem_iff.1 hmem
      right; left
      have hs : (opStep .load [.const (.cap p), .const (.int i)] σ).isSome := by simp [opStep, Store.load, hn, hi, hw]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom.evalL, Atom.eval, hv]) hop⟩
    · exact .inr (.inr (.load hv hn hi))
  | _, _, _, _, _, .store hΓ _ _ _ _, _, _ => by simp at hΓ
  | _, _, _, _, σ, .storeC (p := p) (a₁ := a₁) (a₂ := a₂) hp h₁ h₂ _, hwf, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    obtain ⟨v₁, hv₁, hval₁, hvt₁⟩ := eval_total₂ a₁ h₁
    obtain ⟨i, rfl⟩ := canon_int hval₁ hvt₁
    obtain ⟨v₂, hv₂, hval₂, hvt₂⟩ := eval_total₂ a₂ h₂
    obtain ⟨w, rfl⟩ := canon_int hval₂ hvt₂
    by_cases hi : 0 ≤ i ∧ i < n
    · right; left
      have hs : (opStep .store [.const (.cap p), .const (.int i), .const (.int w)] σ).isSome := by
        simp [opStep, Store.store, hn, hi]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom.evalL, Atom.eval, hv₁, hv₂]) hop⟩
    · exact .inr (.inr (.store hv₁ hn hi))
  | _, _, _, _, _, .free hΓ _ _, _, _ => by simp at hΓ
  | _, _, _, _, σ, .freeC (p := p) hp _, _, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    right; left
    have hs : (opStep .free [.const (.cap p)] σ).isSome := by simp [opStep, Store.free, hn]
    obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨_, .op (by simp [Atom.evalL, Atom.eval]) hop⟩
  | _, _, _, _, _, .app (a₁ := a₁) (a₂ := a₂) _ h₁ h₂, _, _ => by
    obtain ⟨v₁, hv₁, hval₁, hvt₁⟩ := eval_total₂ a₁ h₁
    obtain ⟨v₂, hv₂, -, -⟩ := eval_total₂ a₂ h₂
    right; left
    rcases canon_arr₂ hval₁ hvt₁ with ⟨b, -, rfl, -, -⟩ | ⟨b, -, rfl, -, -⟩
    · exact ⟨_, .pure (.appLam hv₁ hv₂)⟩
    · exact ⟨_, .pure (.appFix hv₁ hv₂)⟩
  | _, _, _, _, _, .ite (a := a) h _ _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₂ a h
    obtain ⟨b, rfl⟩ := canon_bool hval hvt
    right; left
    cases b
    · exact ⟨_, .pure (.iteF hv rfl)⟩
    · exact ⟨_, .pure (.iteT hv rfl)⟩
  | _, _, _, _, _, .case (a := a) h _ _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₂ a h
    right; left
    rcases canon_sum₂ hval hvt with ⟨w, rfl, -, -⟩ | ⟨w, rfl, -, -⟩
    · exact ⟨_, .pure (.caseL hv)⟩
    · exact ⟨_, .pure (.caseR hv)⟩

end VIRL2
