/-
  O95 layer L4, Lean arm (amend-21; OBJECT-L4 H5 (a)): the VALUE claims as CONFIGURATION INVARIANTS on ⟶₄, proved by induction on
  ⟶₄*. N1-V: every terminating run of N1 from the empty store returns 2. The invariant `R1` names every reachable configuration:
  the three setup steps, then `par` with each INC thread at one of five stages, the cell holding w, and
  w + (increments still pending) = 2, at most one thread inside the critical section, the lock held exactly when one is, and a
  thread that has loaded y while holding the lock has y = w; then the join and N1's last critical section.
-/
import VIRL4.Deadlock

namespace VIRL4
open VIRL1 VIRL2

/-- The one cell (base 0, length 1) holds w. -/
def cell (w : Int) (σ : Store) : Prop := σ.R.lookup 0 = some 1 ∧ σ.H.lookup 0 = some w

/-! INC's five stages over lock 0 and region 0 (k = 0 … 4), and the main thread's terms. -/
abbrev A0 : Tm₄ :=
  .letOp .acquire [lockv 0] t4cap <| .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <| .letOp .release [lockv 0, v4 0] t4unit <| .ret (v4 0)
abbrev A1 : Tm₄ :=
  .letOp (.o2 .load) [capv 0, c4 0] t4int <| .letOp (.o2 .store) [capv 0, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .letOp .release [lockv 0, v4 0] t4unit <| .ret (v4 0)
abbrev A2 (y : Int) : Tm₄ :=
  .letOp (.o2 .store) [capv 0, c4 0, padd (c4 y) (c4 1)] t4cap <| .letOp .release [lockv 0, v4 0] t4unit <| .ret (v4 0)
abbrev A3 : Tm₄ := .letOp .release [lockv 0, capv 0] t4unit <| .ret (v4 0)
abbrev A4 : Tm₄ := .ret unitv

abbrev T0 : Tm₄ :=
  .letOp .acquire [lockv 0] t4cap <| .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp .release [lockv 0, v4 1] t4unit <| .ret (v4 1)
abbrev U1 : Tm₄ := .letOp (.o2 .load) [capv 0, c4 0] t4int <| .letOp .release [lockv 0, capv 0] t4unit <| .ret (v4 1)
abbrev U2 : Tm₄ := .letOp .release [lockv 0, capv 0] t4unit <| .ret (c4 2)
abbrev E1' : Tm₄ :=
  .letOp (.o2 .store) [capv 0, c4 0, c4 0] t4cap <| .letOp .newlock [v4 0] t4lock <| .par t4unit t4unit (INC 0) (INC 0) TAIL0
abbrev E2' : Tm₄ := .letOp .newlock [capv 0] t4lock <| .par t4unit t4unit (INC 0) (INC 0) TAIL0

inductive TS : Tm₄ → Nat → Int → Prop where
  | s0 : TS A0 0 0
  | s1 : TS A1 1 0
  | s2 (y : Int) : TS (A2 y) 2 y
  | s3 : TS A3 3 0
  | s4 : TS A4 4 0

def hold (k : Nat) : Bool := decide (1 ≤ k ∧ k ≤ 3)
def pend (k : Nat) : Int := if k ≤ 2 then 1 else 0
def lockOf (b : Bool) : List LockSt := if b then [.held 0] else [.free 0]

def ParOK (k₁ : Nat) (y₁ : Int) (k₂ : Nat) (y₂ w : Int) (L : List LockSt) : Prop :=
  w + pend k₁ + pend k₂ = 2 ∧ ¬ (hold k₁ = true ∧ hold k₂ = true) ∧ L = lockOf (hold k₁ || hold k₂) ∧
    (k₁ = 2 → y₁ = w) ∧ (k₂ = 2 → y₂ = w)

inductive R1 : Config₄ → Prop where
  | init : R1 (N1, ⟨Store.empty, []⟩)
  | alloc {σ} : cell 0 σ → R1 (E1', ⟨σ, []⟩)
  | stored {σ} : cell 0 σ → R1 (E2', ⟨σ, []⟩)
  | par {T₁ T₂ k₁ y₁ k₂ y₂ w σ L} : TS T₁ k₁ y₁ → TS T₂ k₂ y₂ → cell w σ → ParOK k₁ y₁ k₂ y₂ w L →
      R1 (.par t4unit t4unit T₁ T₂ T0, ⟨σ, L⟩)
  | t0 {σ} : cell 2 σ → R1 (T0, ⟨σ, [.free 0]⟩)
  | t1 {σ} : cell 2 σ → R1 (U1, ⟨σ, [.held 0]⟩)
  | t2 {σ} : R1 (U2, ⟨σ, [.held 0]⟩)
  | t3 {s} : R1 (.ret (c4 2), s)

theorem step_letOp_inv {o : Op₄} {as : List Atom₄} {τ : Ty₄} {e : Tm₄} {s : Store₄} {c' : Config₄}
    (h : Step₄ (.letOp o as τ e, s) c') :
    ∃ vs v s', Atom₄.evalL as = some vs ∧ opStep₄ o vs s = some (v, s') ∧ c' = (e.subst 0 v, s') := by
  cases h with
  | op h1 h2 => exact ⟨_, _, _, h1, h2, rfl⟩

theorem cell_load {w : Int} {σ : Store} (hc : cell w σ) : Store.load 0 0 σ = some w := by
  simp [Store.load, hc.1, hc.2]

theorem cell_store {w v : Int} {σ : Store} (hc : cell w σ) :
    Store.store 0 0 v σ = some ⟨σ.H.insert 0 v, σ.R⟩ ∧ cell v ⟨σ.H.insert 0 v, σ.R⟩ := by
  refine ⟨by simp [Store.store, hc.1], hc.1, ?_⟩
  simp [Finmap.lookup_insert]

/-- One INC thread's step, by stage. -/
theorem thread_step {T T' : Tm₄} {k : Nat} {y w : Int} {σ : Store} {L : List LockSt} {s' : Store₄}
    (ht : TS T k y) (hs : Step₄ (T, ⟨σ, L⟩) (T', s')) (hc : cell w σ) (hL : L = [.free 0] ∨ L = [.held 0]) :
    (k = 0 ∧ L = [.free 0] ∧ TS T' 1 0 ∧ s' = ⟨σ, [.held 0]⟩) ∨
    (k = 1 ∧ TS T' 2 w ∧ s' = ⟨σ, L⟩) ∨
    (k = 2 ∧ TS T' 3 0 ∧ s'.locks = L ∧ cell (y + 1) s'.σ) ∨
    (k = 3 ∧ L = [.held 0] ∧ TS T' 4 0 ∧ s' = ⟨σ, [.free 0]⟩) := by
  cases ht with
  | s0 =>
    obtain ⟨vs, v, s'', h1, h2, he⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [lockv 0] = some [lockv 0] from rfl] at h1
    cases h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases hL with rfl | rfl
    · simp [opStep₄, lockv] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨rfl, rfl, TS.s1, rfl⟩
    · simp [opStep₄, lockv] at h2
  | s1 =>
    obtain ⟨vs, v, s'', h1, h2, he⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [capv 0, c4 0] = some [capv 0, c4 0] from rfl] at h1
    cases h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp [opStep₄, lowerV, capv, opStep, cell_load hc] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact Or.inr (Or.inl ⟨rfl, TS.s2 w, rfl⟩)
  | s2 y =>
    obtain ⟨vs, v, s'', h1, h2, he⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [capv 0, c4 0, padd (c4 y) (c4 1)] = some [capv 0, c4 0, c4 (y + 1)] from rfl] at h1
    cases h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hst, hc'⟩ := cell_store (v := y + 1) hc
    simp [opStep₄, lowerV, capv, opStep, hst] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact Or.inr (Or.inr (Or.inl ⟨rfl, TS.s3, rfl, hc'⟩))
  | s3 =>
    obtain ⟨vs, v, s'', h1, h2, he⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [lockv 0, capv 0] = some [lockv 0, capv 0] from rfl] at h1
    cases h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases hL with rfl | rfl
    · simp [opStep₄, lockv, capv] at h2
    · simp [opStep₄, lockv, capv] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, TS.s4, rfl⟩))
  | s4 => cases hs

theorem lockOf_cases (b : Bool) : lockOf b = [.free 0] ∨ lockOf b = [.held 0] := by
  cases b <;> simp [lockOf]

theorem lockOf_of_ok {k₁ k₂ : Nat} {y₁ y₂ w : Int} {L : List LockSt} (h : ParOK k₁ y₁ k₂ y₂ w L) :
    L = [.free 0] ∨ L = [.held 0] := h.2.2.1 ▸ lockOf_cases _

/-- R1 is preserved by every ⟶₄ step. -/
theorem R1_step {c c' : Config₄} (hr : R1 c) (hs : Step₄ c c') : R1 c' := by
  cases hr with
  | init =>
    unfold N1 at hs
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [c4 1] = some [c4 1] from rfl] at h1
    cases h1
    have hnb : Store.nextBase Store.empty = 0 := rfl
    simp [opStep₄, lowerV, opStep, Store.alloc, hnb] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine R1.alloc ⟨?_, ?_⟩ <;> simp [Store.empty, Store.fill]
  | alloc hc =>
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [capv 0, c4 0, c4 0] = some [capv 0, c4 0, c4 0] from rfl] at h1
    cases h1
    obtain ⟨hst, hc'⟩ := cell_store (v := 0) hc
    simp [opStep₄, lowerV, capv, opStep, hst] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact R1.stored hc'
  | stored hc =>
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [capv 0] = some [capv 0] from rfl] at h1
    cases h1
    simp [opStep₄, capv] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact R1.par TS.s0 TS.s0 hc (by simp [ParOK, hold, pend, lockOf])
  | @par T₁ T₂ k₁ y₁ k₂ y₂ w σ L ht₁ ht₂ hc hok =>
    cases hs with
    | @parL _ _ _ _ _ _ _ s' h =>
      rcases thread_step ht₁ h hc (lockOf_of_ok hok) with
        ⟨rfl, rfl, ht', rfl⟩ | ⟨rfl, ht', rfl⟩ | ⟨rfl, ht', hL', hc'⟩ | ⟨rfl, rfl, ht', rfl⟩
      · exact R1.par ht' ht₂ hc (by cases ht₂ <;> simp_all [ParOK, hold, pend, lockOf])
      · exact R1.par ht' ht₂ hc (by cases ht₂ <;> simp_all [ParOK, hold, pend, lockOf])
      · obtain ⟨σ', L'⟩ := s'
        simp only at hL' hc'
        subst hL'
        refine R1.par ht' ht₂ hc' ?_
        have hy := hok.2.2.2.1 rfl
        subst hy
        cases ht₂ <;> simp_all [ParOK, hold, pend, lockOf] <;> omega
      · exact R1.par ht' ht₂ hc (by cases ht₂ <;> simp_all [ParOK, hold, pend, lockOf])
    | @parR _ _ _ _ _ _ _ s' h =>
      rcases thread_step ht₂ h hc (lockOf_of_ok hok) with
        ⟨rfl, rfl, ht', rfl⟩ | ⟨rfl, ht', rfl⟩ | ⟨rfl, ht', hL', hc'⟩ | ⟨rfl, rfl, ht', rfl⟩
      · exact R1.par ht₁ ht' hc (by cases ht₁ <;> simp_all [ParOK, hold, pend, lockOf])
      · exact R1.par ht₁ ht' hc (by cases ht₁ <;> simp_all [ParOK, hold, pend, lockOf])
      · obtain ⟨σ', L'⟩ := s'
        simp only at hL' hc'
        subst hL'
        refine R1.par ht₁ ht' hc' ?_
        have hy := hok.2.2.2.2 rfl
        subst hy
        cases ht₁ <;> simp_all [ParOK, hold, pend, lockOf] <;> omega
      · exact R1.par ht₁ ht' hc (by cases ht₁ <;> simp_all [ParOK, hold, pend, lockOf])
    | parDone hv₁ hv₂ =>
      cases ht₁
      cases ht₂
      obtain ⟨hw, -, hL, -, -⟩ := hok
      simp [hold, pend, lockOf] at hw hL
      subst hL
      have : w = 2 := by omega
      subst this
      exact R1.t0 hc
  | t0 hc =>
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [lockv 0] = some [lockv 0] from rfl] at h1
    cases h1
    simp [opStep₄, lockv] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact R1.t1 hc
  | t1 hc =>
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [capv 0, c4 0] = some [capv 0, c4 0] from rfl] at h1
    cases h1
    simp [opStep₄, lowerV, capv, opStep, cell_load hc] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact R1.t2
  | t2 =>
    obtain ⟨vs, v, s'', h1, h2, rfl⟩ := step_letOp_inv hs
    rw [show Atom₄.evalL [lockv 0, capv 0] = some [lockv 0, capv 0] from rfl] at h1
    cases h1
    simp [opStep₄, lockv, capv] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact R1.t3
  | t3 => cases hs

theorem R1_steps {c c' : Config₄} (h : Steps₄ c c') (hr : R1 c) : R1 c' := by
  induction h with
  | refl => exact hr
  | step hs _ ih => exact ih (R1_step hr hs)

/-- N1-V (H5 (a)): over EVERY interleaving, a terminating run of N1 from the empty store returns 2. -/
theorem N1_V : ∀ c, Steps₄ (N1, ⟨Store.empty, []⟩) c → ∀ a, c.1 = .ret a → a = c4 2 := by
  intro c hc a ha
  have hr := R1_steps hc R1.init
  cases hr <;> simp_all [N1]

end VIRL4
