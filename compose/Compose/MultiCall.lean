/-
  STATUS-vir row 41 (O95). THE SPEC SIDE OF A MULTI-CALL REFINEMENT (the one-invocation limit of RESULTS-3 add. 8):
  what F says about SUCCESSIVE calls when call 2 takes call 1's returned state. It imports only vir's F_exit (no
  spike, no x86lean), so a future machine-level multi-call theorem can take it as its specification.
  ⚠️ It sits in compose/ so the committed whole-tree Lean counts (lean/out) do not move; it moves to lean/ if paris takes it.
-/
import VIR.Exit

namespace VIR.Compose.MultiCall
open VIR VIR.Deep

variable (acl : Principal → TopicId → Bool)

/-- One call, OK exactly when the four guards hold, returning exactly the decremented state and b0 + 24. -/
theorem F_ok_iff (b : Val) (σ : State) (st' out : Val) :
    den acl (F b (.state σ)) = .ret st' out ↔
      ((24 ≤ b.len ∧ ((b.rd 0).toP = MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP)) ∧
        st' = .state (decTokens σ (b.rd 4).toP) ∧ out = b.adv 24) := by
  rw [F_exit]
  simp only [Val.st]
  by_cases h1 : 24 ≤ b.len
  · by_cases h2 : (b.rd 0).toP = MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP
    · simp only [h1, h2, if_true, true_and, DOut.ret.injEq]
      constructor
      · intro ⟨a, c⟩; exact ⟨a.symm, c.symm⟩
      · intro ⟨a, c⟩; exact ⟨a.symm, c.symm⟩
    · simp [h1, h2]
  · simp [h1]

/-- The state threads: call 1 OK with state σ1 ⇒ σ1 is σ with the sender decremented, every other cell kept. -/
theorem ok_state (b : Val) (σ σ1 : State) (o : Val) (h : den acl (F b (.state σ)) = .ret (.state σ1) o) :
    ∀ q, σ1 q = if q = (b.rd 4).toP then σ q - 1 else σ q := by
  obtain ⟨_, hs, _⟩ := (F_ok_iff acl b σ _ o).mp h
  cases hs
  intro q
  by_cases hq : q = (b.rd 4).toP
  · subst hq; simp [decTokens]
  · simp [decTokens, hq]

/-- RATE LIMITING COMPOSES: two successive OK calls from the SAME sender need at least two tokens at the start. -/
theorem two_ok_same_sender (b1 b2 : Val) (σ σ1 σ2 : State) (o1 o2 : Val)
    (h1 : den acl (F b1 (.state σ)) = .ret (.state σ1) o1)
    (h2 : den acl (F b2 (.state σ1)) = .ret (.state σ2) o2)
    (hs : (b2.rd 4).toP = (b1.rd 4).toP) :
    2 ≤ σ (b1.rd 4).toP ∧ σ2 (b1.rd 4).toP = σ (b1.rd 4).toP - 2 := by
  obtain ⟨⟨_, _, _, hpos2⟩, _, _⟩ := (F_ok_iff acl b2 σ1 _ o2).mp h2
  have e1 := ok_state acl b1 σ σ1 o1 h1 (b1.rd 4).toP
  have e2 := ok_state acl b2 σ1 σ2 o2 h2 (b1.rd 4).toP
  simp only [if_true] at e1
  rw [hs] at hpos2 e2
  simp only [if_true] at e2
  omega

/-- A DROP returns no state, so the caller's state is the one it passed: what "memory unchanged on every drop"
    (repaired_refines' drop clauses) refines. -/
theorem drop_no_state (b : Val) (σ : State) (c : Code) (st' out : Val) (h : den acl (F b (.state σ)) = .drop c) :
    den acl (F b (.state σ)) ≠ .ret st' out := by
  rw [h]; simp

end VIR.Compose.MultiCall
