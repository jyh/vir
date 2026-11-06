/-
  O95 layer L4, Lean arm (amend-21; l4/DECLARATIONS-LEAN.md, addendum 2). The triple, defined from ⟶₄ as THREAD-LOCAL SAFETY
  (Vafeiadis, MFPS 2011): `safe₄ I n e L σ Q`, step-indexed, where `I` gives each region base its invariant and the free locks'
  regions live in a SHARED part that `acquire`/`release`/`newlock` move to and from the thread. `Triple₄` quantifies it over every
  index. THE OBJECT'S READING of the triple (L2's, over every interleaving) is `triple₄_adequate`: from any admissible state, no
  ⟶₄*-reachable configuration faults, and every reached `ret` evaluates and satisfies Q. Nothing here edits L1–L3.
-/
import VIRL4.Step4

namespace VIRL4
open VIRL1 VIRL2

/-- The base of the region a lock guards (unchanged by `acquire`/`release`). -/
def LockSt.base : LockSt → Int
  | .free p => p
  | .held p => p

/-- Assertions see the lock table and the thread's store fragment. -/
abbrev Assn₄ := List LockSt → Store → Prop

/-- The environment's lock-table moves: `newlock` appends, `acquire`/`release` keep every base. -/
def Ext (L L' : List LockSt) : Prop := L.map LockSt.base <+: L'.map LockSt.base

theorem Ext.refl (L : List LockSt) : Ext L L := List.prefix_refl _

theorem Ext.trans {L₁ L₂ L₃ : List LockSt} (h₁ : Ext L₁ L₂) (h₂ : Ext L₂ L₃) : Ext L₁ L₃ := List.IsPrefix.trans h₁ h₂

/-- The shared resource of table L: each FREE lock's region (owned exactly) satisfying its invariant, pairwise disjoint. -/
def Shared (I : Int → Assn) : List LockSt → Store → Prop
  | [], σ => σ = Store.empty
  | .free p :: L, σ => ∃ σ₁ σ₂, Store.Disj σ₁ σ₂ ∧ σ = σ₁ ⊎ σ₂ ∧ OwnsRegion p σ₁ ∧ I p σ₁ ∧ Shared I L σ₂
  | .held _ :: L, σ => Shared I L σ

/-- An admissible global state for a thread holding σ: the shared part σS for table L, a frame σF, all disjoint, the whole store WF. -/
def Glob (I : Int → Assn) (σ σS σF : Store) (L : List LockSt) : Prop :=
  Store.Disj σ σS ∧ Store.Disj (σ ⊎ σS) σF ∧ Shared I L σS ∧ Store.WF (σ ⊎ σS ⊎ σF)

/-- Thread-local safety for n steps. -/
def safe₄ (I : Int → Assn) : Nat → Tm₄ → List LockSt → Store → (Atom₄ → Assn₄) → Prop
  | 0, _, _, _, _ => True
  | n + 1, e, L, σ, Q =>
    (∀ a, e = .ret a → ∃ v, Atom₄.eval a = some v ∧ ∀ L', Ext L L' → Q v L' σ) ∧
    (∀ L' σS σF, Ext L L' → Glob I σ σS σF L' →
      ¬ Faults₄ (e, ⟨σ ⊎ σS ⊎ σF, L'⟩) ∧
      ∀ e' s', Step₄ (e, ⟨σ ⊎ σS ⊎ σF, L'⟩) (e', s') →
        ∃ σ' σS', Ext L' s'.locks ∧ Glob I σ' σS' σF s'.locks ∧ s'.σ = σ' ⊎ σS' ⊎ σF ∧ safe₄ I n e' s'.locks σ' Q)

/-- `{P} e {v. Q}` at L4, under invariants I. -/
def Triple₄ (I : Int → Assn) (P : Assn₄) (e : Tm₄) (Q : Atom₄ → Assn₄) : Prop :=
  ∀ n L σ, P L σ → safe₄ I n e L σ Q

/-! ## Adequacy: the triple read over every interleaving. -/

/-- ⟶₄ⁿ, counted (the index the induction spends). -/
inductive StepsN : Nat → Config₄ → Config₄ → Prop where
  | refl (c) : StepsN 0 c c
  | step {k c c' c''} : Step₄ c c' → StepsN k c' c'' → StepsN (k + 1) c c''

theorem Steps₄.toN {c c' : Config₄} (h : Steps₄ c c') : ∃ k, StepsN k c c' := by
  induction h with
  | refl c => exact ⟨0, .refl c⟩
  | step hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .step hs hk⟩

theorem adequate_aux {I : Int → Assn} {Q : Atom₄ → Assn₄} :
    ∀ {k : Nat} {c c' : Config₄}, StepsN k c c' →
    ∀ (n : Nat) (e : Tm₄) (L : List LockSt) (σ σS σF : Store),
      c = (e, ⟨σ ⊎ σS ⊎ σF, L⟩) → Glob I σ σS σF L → safe₄ I (n + k + 1) e L σ Q →
      ¬ Faults₄ c' ∧
      (∀ a, c'.1 = .ret a → ∃ v σ' σS', Atom₄.eval a = some v ∧ Glob I σ' σS' σF c'.2.locks ∧
        c'.2.σ = σ' ⊎ σS' ⊎ σF ∧ Q v c'.2.locks σ') := by
  intro k c c' hk
  induction hk with
  | refl c =>
    intro n e L σ σS σF hc hg hs
    subst hc
    obtain ⟨hterm, hstep⟩ := hs
    refine ⟨(hstep L σS σF (Ext.refl L) hg).1, fun a ha => ?_⟩
    obtain ⟨v, hv, hQ⟩ := hterm a ha
    exact ⟨v, σ, σS, hv, hg, rfl, hQ L (Ext.refl L)⟩
  | @step k c c₁ c'' h1 _ ih =>
    intro n e L σ σS σF hc hg hs
    subst hc
    have hs' : safe₄ I ((n + k + 1) + 1) e L σ Q := by
      have : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
      rw [← this]; exact hs
    obtain ⟨_, hstep⟩ := hs'
    obtain ⟨e', s'⟩ := c₁
    obtain ⟨σ', σS', _, hg', hσ, hsafe⟩ := (hstep L σS σF (Ext.refl L) hg).2 e' s' h1
    obtain ⟨σs, Ls⟩ := s'
    simp only at hσ hg' hsafe
    subst hσ
    exact ih n e' Ls σ' σS' σF rfl hg' hsafe

/-- THE OBJECT'S TRIPLE (OBJECT-L4 H3 (a)): a `Triple₄` gives, from any admissible state, on EVERY ⟶₄* run: no fault, and every
  terminal `ret a` evaluates to v with the thread's final fragment satisfying `Q v`, the frame untouched, the store WF. -/
theorem triple₄_adequate {I : Int → Assn} {P : Assn₄} {e : Tm₄} {Q : Atom₄ → Assn₄} (h : Triple₄ I P e Q)
    {L : List LockSt} {σ σS σF : Store} (hP : P L σ) (hg : Glob I σ σS σF L) :
    ∀ c, Steps₄ (e, ⟨σ ⊎ σS ⊎ σF, L⟩) c →
      ¬ Faults₄ c ∧
      (∀ a, c.1 = .ret a → ∃ v σ' σS', Atom₄.eval a = some v ∧ Glob I σ' σS' σF c.2.locks ∧
        c.2.σ = σ' ⊎ σS' ⊎ σF ∧ Q v c.2.locks σ') := by
  intro c hc
  obtain ⟨k, hk⟩ := hc.toN
  exact adequate_aux hk 0 e L σ σS σF rfl hg (h _ L σ hP)

/-! ## Controls: the triple is neither vacuous nor indiscriminate. -/

/-- A fault reachable in zero steps from an admissible state refutes every triple whose precondition admits it. -/
theorem not_triple₄_of_faults {I : Int → Assn} {P : Assn₄} {e : Tm₄} {Q : Atom₄ → Assn₄}
    {L : List LockSt} {σ σS σF : Store} (hP : P L σ) (hg : Glob I σ σS σF L)
    (hf : Faults₄ (e, ⟨σ ⊎ σS ⊎ σF, L⟩)) : ¬ Triple₄ I P e Q := by
  intro h
  exact (h 1 L σ hP).2 L σS σF (Ext.refl L) hg |>.1 hf

/-- Non-vacuous: `ret ()` from emp, ending in emp. -/
theorem triple₄_ret_unit (I : Int → Assn) :
    Triple₄ I (fun _ σ => σ = Store.empty) (.ret unitv) (fun v _ σ => v = unitv ∧ σ = Store.empty) := by
  intro n L σ hP
  cases n with
  | zero => trivial
  | succ n =>
    refine ⟨fun a ha => ?_, fun L' σS σF _ _ => ⟨fun hf => hf.1 trivial, fun e' s' hs => by cases hs⟩⟩
    cases ha
    exact ⟨unitv, rfl, fun _ _ => ⟨rfl, hP⟩⟩

theorem disj_empty_empty : Store.Disj Store.empty Store.empty := by
  simp [Store.Disj, Store.empty, Finmap.Disjoint, Finmap.notMem_empty]

theorem wf_empty : Store.WF Store.empty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Store.empty, Finmap.notMem_empty]

theorem glob_empty (I : Int → Assn) : Glob I Store.empty Store.empty Store.empty [] := by
  refine ⟨disj_empty_empty, ?_, rfl, ?_⟩
  · rw [Store.empty_union]; exact disj_empty_empty
  · rw [Store.empty_union, Store.empty_union]; exact wf_empty

/-- Discriminating: applying a non-function faults at once, so it has NO triple from emp, whatever Q. -/
theorem app_unit_no_triple (I : Int → Assn) (Q : Atom₄ → Assn₄) :
    ¬ Triple₄ I (fun _ σ => σ = Store.empty) (.app unitv unitv) Q := by
  refine not_triple₄_of_faults (L := []) (σS := Store.empty) (σF := Store.empty) rfl (glob_empty I) ⟨id, ?_, ?_⟩
  · intro c' hs
    cases hs with
    | appLam h1 _ => simp [Atom₄.eval, unitv] at h1
    | appFix h1 _ => simp [Atom₄.eval, unitv] at h1
  · intro hw
    cases hw

end VIRL4
