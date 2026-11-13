/-
  O95 layer L5, Lean arm (amend-24 LV4). PROGRESS up to an INDEX fault (errata L2-E1, L2-E2 carried up), L2's `progress_rt` restated
  for RT₅ (ported text; part of `L5.syntaxCopy`): a closed runtime-typed term whose owned regions are live is terminal (`ret` or
  `retK`), steps, or index-faults. THE L1′ CASES: a closed `appK` lends constants only (`CapsRT.closed`), so it steps into the
  callee; a `letK` whose head is terminal steps by `letKRet` (a `retK`) or `letKRet0` (a `ret`, j = 0; DECLARATIONS Addendum 2).
-/
import VIRL5.Preservation5

namespace VIRL5
open VIRL1 VIRL2

theorem canon_arr₅ {v : Atom₅} {τ₁ k τ₂} (hv : v.IsValue) (h : HasTypeA₅ [] v (.arr τ₁ k τ₂)) :
    (∃ e, v = .lam τ₁ k e) ∨ (∃ e, v = .fix τ₁ k τ₂ e) := by
  cases v <;> simp [Atom₅.IsValue] at hv <;> cases h
  all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩

theorem RT₅.retK_inv {Γ Δ Ω a ds τ k} (h : RT₅ Γ Δ Ω (.retK a ds) τ k) :
    k = ds.length ∧ τ.hasCap = false ∧ HasTypeA₅ Γ a τ ∧ CapsRT Γ Δ Ω ds := by
  cases h; exact ⟨rfl, ‹_›, ‹_›, ‹_›⟩

theorem op5_of {o : Op} {cs : List Const} {σ : Store} {v : Atom₂} {σ' : Store}
    (h : opStep o (cs.map Atom.const) σ = some (v, σ')) : opStep₅ o (cs.map Atom₅.const) σ = some (ιA v, σ') := by
  rw [opStep₅_consts, h]; rfl

theorem progress₅ : ∀ {Δ Ω e τ k} {σ : Store}, RT₅ [] Δ Ω e τ k → Store.WF σ → (∀ p ∈ Ω, ∃ n, σ.R.lookup p = some n) →
    e.IsTerminal ∨ (∃ c, Step₅ (e, σ) c) ∨ IndexFault₅ (e, σ)
  | _, _, _, _, _, _, .ret _ _, _, _ => .inl trivial
  | _, _, _, _, _, _, .retCap hΓ _, _, _ => by simp at hΓ
  | _, _, _, _, _, _, .retCapC _, _, _ => .inl trivial
  | _, _, _, _, _, σ, .letE (e₁ := e₁) _ hp _ h₁ _, hwf, hown => by
    have hown₁ : ∀ p ∈ _, ∃ n, σ.R.lookup p = some n := fun p hp' => hown p (hp.symm.subset (List.mem_append_left _ hp'))
    rcases progress₅ h₁ hwf hown₁ with ht | ⟨⟨e₁', σ'⟩, hs⟩ | hf
    · cases e₁ with
      | ret a =>
        right; left
        cases h₁ with
        | ret _ ha =>
          obtain ⟨v, hv, -, -⟩ := eval_total₅ a ha
          exact ⟨_, (.letRet hv)⟩
        | retCap hΓ _ => simp at hΓ
        | retCapC _ => exact ⟨_, (.letRet rfl)⟩
      | retK a ds =>
        right; left
        obtain ⟨hk, -, ha, -⟩ := RT₅.retK_inv h₁
        obtain rfl : ds = [] := List.eq_nil_of_length_eq_zero hk.symm
        obtain ⟨v, hv, -, -⟩ := eval_total₅ a ha
        exact ⟨_, .letRetK0 hv⟩
      | _ => exact ht.elim
    · exact .inr (.inl ⟨_, .letStep hs⟩)
    · exact .inr (.inr (.letE hf))
  | _, _, _, _, _, σ, .alloc (a := a) ha _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₅ a ha
    obtain ⟨k, rfl⟩ := canon_int₅ hval hvt
    by_cases hk : 0 < k
    · right; left
      have hs : (opStep .alloc [.const (.int k)] σ).isSome := by simp [opStep, Store.alloc, hk]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom₅.evalL, hv]) (op5_of (cs := [Const.int k]) hop)⟩
    · exact .inr (.inr (.alloc hv (by omega)))
  | _, _, _, _, _, _, .load hΓ _ _ _, _, _ => by simp at hΓ
  | _, _, _, _, _, σ, .loadC (p := p) (a := a) hp ha _, hwf, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₅ a ha
    obtain ⟨i, rfl⟩ := canon_int₅ hval hvt
    by_cases hi : 0 ≤ i ∧ i < n
    · have hmem : p + i ∈ σ.H := (hwf.domH _).2 ⟨p, n, hn, by unfold Store.InRegion; omega⟩
      obtain ⟨w, hw⟩ := Finmap.mem_iff.1 hmem
      right; left
      have hs : (opStep .load [.const (.cap p), .const (.int i)] σ).isSome := by simp [opStep, Store.load, hn, hi, hw]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom₅.evalL, Atom₅.eval, hv]) (op5_of (cs := [Const.cap p, Const.int i]) hop)⟩
    · exact .inr (.inr (.load hv hn hi))
  | _, _, _, _, _, _, .store hΓ _ _ _ _, _, _ => by simp at hΓ
  | _, _, _, _, _, σ, .storeC (p := p) (a₁ := a₁) (a₂ := a₂) hp h₁ h₂ _, hwf, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    obtain ⟨v₁, hv₁, hval₁, hvt₁⟩ := eval_total₅ a₁ h₁
    obtain ⟨i, rfl⟩ := canon_int₅ hval₁ hvt₁
    obtain ⟨v₂, hv₂, hval₂, hvt₂⟩ := eval_total₅ a₂ h₂
    obtain ⟨w, rfl⟩ := canon_int₅ hval₂ hvt₂
    by_cases hi : 0 ≤ i ∧ i < n
    · right; left
      have hs : (opStep .store [.const (.cap p), .const (.int i), .const (.int w)] σ).isSome := by
        simp [opStep, Store.store, hn, hi]
      obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨_, .op (by simp [Atom₅.evalL, Atom₅.eval, hv₁, hv₂]) (op5_of (cs := [Const.cap p, Const.int i, Const.int w]) hop)⟩
    · exact .inr (.inr (.store hv₁ hn hi))
  | _, _, _, _, _, _, .free hΓ _ _, _, _ => by simp at hΓ
  | _, _, _, _, _, σ, .freeC (p := p) hp _, _, hown => by
    obtain ⟨n, hn⟩ := hown p hp
    right; left
    have hs : (opStep .free [.const (.cap p)] σ).isSome := by simp [opStep, Store.free, hn]
    obtain ⟨⟨v', σ'⟩, hop⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨_, .op (by simp [Atom₅.evalL, Atom₅.eval]) (op5_of (cs := [Const.cap p]) hop)⟩
  | _, _, _, _, _, _, .app (a₁ := a₁) (a₂ := a₂) _ h₁ h₂, _, _ => by
    obtain ⟨v₁, hv₁, hval₁, hvt₁⟩ := eval_total₅ a₁ h₁
    obtain ⟨v₂, hv₂, -, -⟩ := eval_total₅ a₂ h₂
    right; left
    rcases canon_arr₅ hval₁ hvt₁ with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨_, (.appLam hv₁ hv₂)⟩
    · exact ⟨_, (.appFix hv₁ hv₂)⟩
  | _, _, _, _, _, _, .ite (a := a) h _ _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₅ a h
    obtain ⟨b, rfl⟩ := canon_bool₅ hval hvt
    right; left
    cases b
    · exact ⟨_, (.iteF hv rfl)⟩
    · exact ⟨_, (.iteT hv rfl)⟩
  | _, _, _, _, _, _, .case (a := a) h _ _, _, _ => by
    obtain ⟨v, hv, hval, hvt⟩ := eval_total₅ a h
    right; left
    rcases canon_sum₅ hval hvt with ⟨w, rfl, -, -⟩ | ⟨w, rfl, -, -⟩
    · exact ⟨_, (.caseL hv)⟩
    · exact ⟨_, (.caseR hv)⟩
  | _, _, _, _, _, _, .retK _ _ _, _, _ => .inl trivial
  | _, _, _, _, _, _, .appK (a₁ := a₁) (a₂ := a₂) h₁ h₂ hx, _, _ => by
    obtain ⟨ps, rfl, -⟩ := CapsRT.closed hx
    obtain ⟨v₁, hv₁, hval₁, hvt₁⟩ := eval_total₅ a₁ h₁
    obtain ⟨v₂, hv₂, -, -⟩ := eval_total₅ a₂ h₂
    right; left
    rcases canon_arr₅ hval₁ hvt₁ with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨_, .appKLam hv₁ hv₂ (evalL_capConsts ps) rfl⟩
    · exact ⟨_, .appKFix hv₁ hv₂ (evalL_capConsts ps) rfl⟩
  | _, _, _, _, _, σ, .letK (e₁ := e₁) _ hp hc h₁ _, hwf, hown => by
    have hown₁ : ∀ p ∈ _, ∃ n, σ.R.lookup p = some n := fun p hp' => hown p (hp.symm.subset (List.mem_append_left _ hp'))
    rcases progress₅ h₁ hwf hown₁ with ht | ⟨⟨e₁', σ'⟩, hs⟩ | hf
    · cases e₁ with
      | ret a =>
        right; left
        cases h₁ with
        | ret _ ha =>
          obtain ⟨v, hv, -, -⟩ := eval_total₅ a ha
          exact ⟨_, .letKRet0 hv⟩
        | retCap hΓ _ => simp at hΓ
        | retCapC _ => simp [Ty₅.hasCap, t5cap] at hc
      | retK a ds =>
        right; left
        cases h₁ with
        | retK _ ha hx =>
          obtain ⟨ps, rfl, -⟩ := CapsRT.closed hx
          obtain ⟨v, hv, -, -⟩ := eval_total₅ a ha
          exact ⟨_, .letKRet hv (evalL_capConsts ps) rfl⟩
      | _ => exact ht.elim
    · exact .inr (.inl ⟨_, .letKStep hs⟩)
    · exact .inr (.inr (.letK hf))

end VIRL5
