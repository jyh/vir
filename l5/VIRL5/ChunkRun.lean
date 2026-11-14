/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, BRIDGE (ii) of BANK-72, the part that does not depend on the mode term).
  Correct.lean's `scopy_run` / `copy_run` are inductions over k ONE-item steps. A chunked mode advances min(k, C) items per step.
  `chunk_run` is that induction once, over ANY step function S and any state advance `adv` that is additive: from a chunk-step
  hypothesis and an end-step hypothesis it gives the same conclusion `scopy_run` gives, reached by S. `scopyAdv_add` is SCOPY's
  advance (pos + 8c, out ++ the next c input bytes), additive with no bound on the bytes.
-/
import VIRL5.Run5
import VIRDeflate.Correct

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate VIRDeflate.Step

/-- k steps of a step function. -/
def iterF (S : Store → Option Store) : Nat → Store → Option Store
  | 0, σ => some σ
  | k + 1, σ => (S σ).bind (iterF S k)

/-- σ' is reachable from σ by S. -/
def ReachF (S : Store → Option Store) (σ σ' : Store) : Prop := ∃ k, iterF S k σ = some σ'

theorem iterF_add (S : Store → Option Store) : ∀ (a b : Nat) (σ : Store),
    iterF S (a + b) σ = (iterF S a σ).bind (iterF S b)
  | 0, b, σ => by simp [iterF]
  | a + 1, b, σ => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iterF]
    cases S σ with
    | none => rfl
    | some σ1 => exact iterF_add S a b σ1

theorem ReachF.step {S : Store → Option Store} {σ σ1 : Store} (h : S σ = some σ1) : ReachF S σ σ1 :=
  ⟨1, by simp [iterF, h]⟩

theorem ReachF.trans {S : Store → Option Store} {σ₁ σ₂ σ₃ : Store} (h₁ : ReachF S σ₁ σ₂) (h₂ : ReachF S σ₂ σ₃) :
    ReachF S σ₁ σ₃ := by
  obtain ⟨a, ha⟩ := h₁; obtain ⟨b, hb⟩ := h₂
  exact ⟨a + b, by rw [iterF_add, ha]; exact hb⟩

/-- **The chunked run.** P k σ s: k items are pending at store σ with abstract state s. Each step with k ≠ 0 pending advances
  c = min k C items (C ≥ 1); the step with none pending ends in Q. Then from P k σ s, S reaches a Q-store whose state is s
  advanced by k, provided adv is additive. -/
theorem chunk_run {α : Type} {S : Store → Option Store} {C : Nat} (hC : 1 ≤ C)
    {P : Nat → Store → α → Prop} {Q : Store → α → Prop} {adv : α → Nat → α}
    (hadd : ∀ s a b, adv (adv s a) b = adv s (a + b)) (hzero : ∀ s, adv s 0 = s)
    (hnext : ∀ k σ s, P k σ s → k ≠ 0 → ∃ σ1, S σ = some σ1 ∧ P (k - min k C) σ1 (adv s (min k C)))
    (hend : ∀ σ s, P 0 σ s → ∃ σ1, S σ = some σ1 ∧ Q σ1 s) :
    ∀ k σ s, P k σ s → ∃ σ', ReachF S σ σ' ∧ Q σ' (adv s k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro σ s hP
    by_cases hk : k = 0
    · subst hk
      obtain ⟨σ1, hS, hQ⟩ := hend σ s hP
      exact ⟨σ1, ReachF.step hS, by rw [hzero]; exact hQ⟩
    · obtain ⟨σ1, hS, hP1⟩ := hnext k σ s hP hk
      have hlt : k - min k C < k := by omega
      obtain ⟨σ', hR, hQ⟩ := ih _ hlt σ1 _ hP1
      refine ⟨σ', (ReachF.step hS).trans hR, ?_⟩
      rw [hadd, show min k C + (k - min k C) = k by omega] at hQ
      exact hQ

/-- SCOPY's state advance: c input bytes copied to the output, the bit position moved by 8c. -/
def scopyAdv (b : Array Nat) (st : St) (c : Nat) : St :=
  ⟨st.pos + 8 * c, st.out ++ b.extract (st.pos / 8) (st.pos / 8 + c)⟩

theorem scopyAdv_zero (b : Array Nat) (st : St) : scopyAdv b st 0 = st := by
  cases st; simp [scopyAdv]

/-- Two adjacent extracts are one. -/
theorem extract_append_extract' (b : Array Nat) (q c d : Nat) :
    b.extract q (q + c) ++ b.extract (q + c) (q + c + d) = b.extract q (q + (c + d)) := by
  apply Array.ext'
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_drop_take]
  rw [show q + c - q = c by omega, show q + c + d - (q + c) = d by omega, show q + (c + d) - q = c + d by omega,
    List.take_add, List.drop_drop]

theorem scopyAdv_add (b : Array Nat) (st : St) (c d : Nat) :
    scopyAdv b (scopyAdv b st c) d = scopyAdv b st (c + d) := by
  simp only [scopyAdv]
  have e : (st.pos + 8 * c) / 8 = st.pos / 8 + c := by omega
  rw [e, Array.append_assoc, extract_append_extract', show st.pos + 8 * c + 8 * d = st.pos + 8 * (c + d) by ring]

/-- COPY's run is additive: S7's `copyBack` of a + b bytes is b bytes after a. -/
theorem copyBack_add (d : Nat) : ∀ (a b : Nat) (o : Array Nat), copyBack d (a + b) o = copyBack d b (copyBack d a o)
  | 0, b, o => by simp [copyBack]
  | a + 1, b, o => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [copyBack]
    exact copyBack_add d a b _

/-- COPY's state advance: c bytes copied back from distance d; the bit position does not move. -/
def copyAdv (d : Nat) (st : St) (c : Nat) : St := ⟨st.pos, copyBack d c st.out⟩

theorem copyAdv_zero (d : Nat) (st : St) : copyAdv d st 0 = st := by
  cases st; simp [copyAdv, copyBack]

theorem copyAdv_add (d : Nat) (st : St) (c e : Nat) : copyAdv d (copyAdv d st c) e = copyAdv d st (c + e) := by
  simp only [copyAdv, copyBack_add]

end VIRL5
