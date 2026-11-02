/-
  O95 VIR program, Lean arm. The BINDER LEMMAS (amend-11 V2: D1's operators are `subst`, and `ins` its context/environment
  counterpart). Everything in this file exists because the encoding is first-order; HOAS would take it from the framework.
-/
import VIRP.Typing

namespace VIRP

theorem getElem?_ins {α : Type} : ∀ (k : Nat) (x : α) (l : List α) (n : Nat), k ≤ l.length →
    (ins k x l)[n]? = if n = k then some x else if k < n then l[n - 1]? else l[n]?
  | 0, x, l, 0, _ => by simp [ins]
  | 0, x, l, n + 1, _ => by simp [ins]
  | k + 1, x, [], n, h => by simp at h
  | k + 1, x, y :: l, 0, _ => by simp [ins]
  | k + 1, x, y :: l, n + 1, h => by
      simp only [ins, List.getElem?_cons_succ]
      rw [getElem?_ins k x l n (by simpa using h)]
      by_cases h1 : n = k
      · simp [h1]
      · by_cases h2 : k < n
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp [h1, h2, show k + 1 < m + 1 + 1 by omega]
        · simp [h1, h2, show ¬ (k + 1 < n + 1) by omega, show ¬ (n + 1 = k + 1) by omega]

theorem length_ins {α : Type} : ∀ (k : Nat) (x : α) (l : List α), k ≤ l.length → (ins k x l).length = l.length + 1
  | 0, _, _, _ => by simp [ins]
  | k + 1, _, [], h => by simp at h
  | k + 1, x, _ :: l, h => by simp [ins, length_ins k x l (by simpa using h)]

theorem mem_ins_of_mem {α : Type} {y : α} : ∀ (k : Nat) (x : α) (l : List α), y ∈ l → y ∈ ins k x l
  | 0, _, _, h => by simp [ins, h]
  | k + 1, _, [], h => by simp at h
  | k + 1, x, z :: l, h => by
      simp only [ins, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_ins_of_mem k x l h)

/-- Consuming slot `n` of an extended context. -/
theorem set_ins {α : Type} (z : α) : ∀ (k : Nat) (x : α) (l : List α) (n : Nat), k ≤ l.length →
    (ins k x l).set n z = if n = k then ins k z l else if k < n then ins k x (l.set (n - 1) z) else ins k x (l.set n z)
  | 0, x, l, 0, _ => by simp [ins]
  | 0, x, l, n + 1, _ => by simp [ins]
  | k + 1, x, [], n, h => by simp at h
  | k + 1, x, y :: l, 0, _ => by simp [ins]
  | k + 1, x, y :: l, n + 1, h => by
      simp only [ins, List.set_cons_succ]
      rw [set_ins z k x l n (by simpa using h)]
      by_cases h1 : n = k
      · simp [h1]
      · by_cases h2 : k < n
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp [h1, h2, show k + 1 < m + 1 + 1 by omega, ins]
        · simp [h1, h2, show ¬ (k + 1 < n + 1) by omega, show ¬ (n + 1 = k + 1) by omega, ins]

/-- A closed atom is unchanged by substitution. -/
theorem ATy.subst_closed {a : Atom} {τ : Ty} (h : ATy [] a τ) (k : Nat) (v : Atom) : a.subst k v = a := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h <;> subst hΓ <;> simp_all [Atom.subst]

/-- Weakening from the empty context (closed atoms are typed anywhere). -/
theorem ATy.weaken {a : Atom} {τ : Ty} (h : ATy [] a τ) (Γ : Ctx) : ATy Γ a τ := by
  generalize hΓ : ([] : Ctx) = Δ at h
  induction h <;> subst hΓ
  all_goals first | (simp at *) | constructor <;> assumption

/-- The substitution lemma for atom typing. -/
theorem ATy.subst {Γ : Ctx} {k : Nat} {o : Option Ty} {a : Atom} {τ : Ty} {v : Atom}
    (h : ATy (ins k o Γ) a τ) (hk : k ≤ Γ.length) (hv : ∀ τ', o = some τ' → ATy [] v τ') :
    ATy Γ (a.subst k v) τ := by
  generalize hΔ : ins k o Γ = Δ at h
  induction h <;> subst hΔ <;> simp only [Atom.subst]
  case var n τ hn =>
    rw [getElem?_ins k o Γ n hk] at hn
    by_cases h1 : n = k
    · simp only [h1, if_true] at hn ⊢; exact (hv τ (by simpa using hn)).weaken Γ
    · by_cases h2 : k < n
      · simp only [h1, h2, if_false, if_true] at hn ⊢; exact .var hn
      · simp only [h1, h2, if_false] at hn ⊢; exact .var hn
  all_goals (constructor <;> assumption)

/-- The substitution lemma for consumption. -/
theorem Use.subst {Γ : Ctx} {k : Nat} {o : Option Ty} {a : Atom} {τ : Ty} {Γ'' : Ctx} {v : Atom}
    (h : Use (ins k o Γ) a τ Γ'') (hk : k ≤ Γ.length) (hv : ∀ τ', o = some τ' → ATy [] v τ') :
    ∃ Γ' o', Use Γ (a.subst k v) τ Γ' ∧ Γ'' = ins k o' Γ' ∧ (o' = o ∨ o' = none) ∧ Γ'.length = Γ.length := by
  cases h with
  | var hn =>
    rename_i n
    have hn' := hn
    rw [getElem?_ins k o Γ n hk] at hn'
    rw [set_ins none k o Γ n hk]
    by_cases h1 : n = k
    · simp only [h1, if_true, Atom.subst] at hn' ⊢
      exact ⟨Γ, none, .val (hv τ (by simpa using hn')), rfl, Or.inr rfl, rfl⟩
    · by_cases h2 : k < n
      · simp only [h1, h2, if_false, if_true, Atom.subst] at hn' ⊢
        exact ⟨_, o, .var hn', rfl, Or.inl rfl, by simp⟩
      · simp only [h1, h2, if_false, Atom.subst] at hn' ⊢
        exact ⟨_, o, .var hn', rfl, Or.inl rfl, by simp⟩
  | val ha =>
    exact ⟨Γ, o, by rw [ha.subst_closed]; exact .val ha, rfl, Or.inl rfl, rfl⟩

/-- THE SUBSTITUTION LEMMA for expression typing. -/
theorem HasType.subst : ∀ (e : Tm) {Γ : Ctx} {k : Nat} {o : Option Ty} {v : Atom},
    HasType (ins k o Γ) e → k ≤ Γ.length → (∀ τ', o = some τ' → ATy [] v τ') → HasType Γ (e.subst k v)
  | .letLinDec s p e, Γ, k, o, v, h, hk, hv => by
    cases h with
    | letLinDec hs hp he =>
      obtain ⟨Γ', o', hs', rfl, ho', hl⟩ := hs.subst hk hv
      refine .letLinDec hs' (hp.subst hk hv) ?_
      exact HasType.subst e (Γ := some .tok :: Γ') (k := k + 1) (o := o') he (by simp [hl, hk])
        (by rcases ho' with rfl | rfl <;> simp_all)
  | .advance b i e, Γ, k, o, v, h, hk, hv => by
    cases h with
    | advance hb he =>
      obtain ⟨Γ', o', hb', rfl, ho', hl⟩ := hb.subst hk hv
      refine .advance hb' ?_
      exact HasType.subst e (Γ := some .slice :: Γ') (k := k + 1) (o := o') he (by simp [hl, hk])
        (by rcases ho' with rfl | rfl <;> simp_all)
  | .readU32 b j e, Γ, k, o, v, h, hk, hv => by
    cases h with
    | readU32 hb he =>
      exact .readU32 (hb.subst hk hv) (HasType.subst e (Γ := some .int :: Γ) (k := k + 1) (o := o) he (by simp [hk]) hv)
  | .guard c ok err, Γ, k, o, v, h, hk, hv => by
    cases h with
    | guard hc hok herr => exact .guard (hc.subst hk hv) (HasType.subst ok hok hk hv) (HasType.subst err herr hk hv)
  | .ret s b, Γ, k, o, v, h, hk, hv => by
    cases h with
    | ret hs hb hno =>
      obtain ⟨Γ', o', hs', rfl, ho', hl⟩ := hs.subst hk hv
      refine .ret hs' (hb.subst (by omega) (by rcases ho' with rfl | rfl <;> simp_all)) ?_
      exact fun hm => hno (mem_ins_of_mem k o' Γ' hm)
  | .drop c, _, _, _, _, _, _, _ => .drop

/-- The substitution lemma for the denotation: substituting a closed value = extending the environment. -/
theorem Atom.eval_subst {v : Atom} {x : Val} (hv : ∀ env σ, v.eval env σ = some x) :
    ∀ (a : Atom) (k : Nat) (env : List Val) (σ : Store), k ≤ env.length →
      (a.subst k v).eval env σ = a.eval (ins k x env) σ
  | .var n, k, env, σ, hk => by
    simp only [Atom.subst, Atom.eval]
    rw [getElem?_ins k x env n hk]
    by_cases h1 : n = k
    · simp [h1, hv]
    · by_cases h2 : k < n <;> simp [h1, h2, Atom.eval]
  | .lit _, _, _, _, _ | .bool _, _, _, _, _ | .sl _, _, _, _, _ | .tok, _, _, _, _ | .magic, _, _, _, _ => rfl
  | .len a, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk]
  | .ge a b, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk, Atom.eval_subst hv b k env σ hk]
  | .eq a b, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk, Atom.eval_subst hv b k env σ hk]
  | .and a b, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk, Atom.eval_subst hv b k env σ hk]
  | .canAccess a b, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk, Atom.eval_subst hv b k env σ hk]
  | .hasTokens a b, k, env, σ, hk => by simp only [Atom.subst, Atom.eval, Atom.eval_subst hv a k env σ hk, Atom.eval_subst hv b k env σ hk]

theorem den_subst {v : Atom} {x : Val} (hv : ∀ env σ, v.eval env σ = some x) :
    ∀ (e : Tm) (k : Nat) (env : List Val) (σ : Store), k ≤ env.length →
      den (e.subst k v) env σ = den e (ins k x env) σ
  | .letLinDec s p e, k, env, σ, hk => by
    simp only [Tm.subst, den, Atom.eval_subst hv s k env σ hk, Atom.eval_subst hv p k env σ hk]
    split <;> try rfl
    exact den_subst hv e (k + 1) _ _ (by simp [hk])
  | .advance b i e, k, env, σ, hk => by
    simp only [Tm.subst, den, Atom.eval_subst hv b k env σ hk]
    split <;> try rfl
    exact den_subst hv e (k + 1) _ _ (by simp [hk])
  | .readU32 b j e, k, env, σ, hk => by
    simp only [Tm.subst, den, Atom.eval_subst hv b k env σ hk]
    split <;> try rfl
    exact den_subst hv e (k + 1) _ _ (by simp [hk])
  | .guard c ok err, k, env, σ, hk => by
    simp only [Tm.subst, den, Atom.eval_subst hv c k env σ hk, den_subst hv ok k env σ hk, den_subst hv err k env σ hk]
  | .ret s b, k, env, σ, hk => by
    simp only [Tm.subst, den, Atom.eval_subst hv s k env σ hk, Atom.eval_subst hv b k env σ hk]
  | .drop c, _, _, _, _ => rfl

end VIRP
