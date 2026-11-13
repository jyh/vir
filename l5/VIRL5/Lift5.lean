/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5 infrastructure 2): a LIFTED term runs as its source. `run₅ n` of an embedded
  configuration is the embedding of `run₂ n` of the source, at every fuel n. This is why a mode left as ιE of DEFLATE's own term
  keeps every ⟶₂ fact DEFLATE proved about it (its stepS lemmas run at KSTEP): one rewrite carries them. The proof needs only
  LV3's CE in both directions (ce_fwd, ce_bwd) and the two step functions' soundness and completeness.
-/
import VIRL5.Run5
import VIRL5.Embed5

namespace VIRL5
open VIRL1 VIRL2

/-- The embedding of a configuration. -/
def ιC (c : Config) : Config₅ := (ιE c.1, c.2)

/-- One step: ⟶₅'s step function on an embedded term is the embedding of ⟶₂'s. -/
theorem stepFn₅_ι (e : Tm₂) (σ : Store) : stepFn₅ (ιE e) σ = (stepFn₂ e σ).map ιC := by
  cases h : stepFn₂ e σ with
  | some c =>
    have s := stepFn₂_sound h
    exact stepFn₅_complete (ce_fwd s)
  | none =>
    cases h₅ : stepFn₅ (ιE e) σ with
    | none => rfl
    | some c' =>
      obtain ⟨e', σ', s, -⟩ := ce_bwd (stepFn₅_sound h₅) e σ rfl
      have := VIRDeflate.Step.stepFn₂_complete s
      rw [h] at this
      exact absurd this (by simp)

/-- **The lift lemma.** At every fuel n, running an embedded configuration under ⟶₅ is embedding the ⟶₂ run. -/
theorem run₅_ι : ∀ (n : Nat) (c : Config), run₅ n (ιC c) = ιC (run₂ n c)
  | 0, _ => rfl
  | n + 1, c => by
    show (match stepFn₅ (ιE c.1) c.2 with | some c' => run₅ n c' | none => ιC c) = _
    rw [stepFn₅_ι]
    simp only [run₂]
    cases stepFn₂ c.1 c.2 with
    | none => rfl
    | some c' => exact run₅_ι n c'

/-- The same, in the pair form DEFLATE's stepS uses. -/
theorem run₅_ιE (n : Nat) (t : Tm₂) (σ : Store) :
    run₅ n (ιE t, σ) = (ιE (run₂ n (t, σ)).1, (run₂ n (t, σ)).2) :=
  run₅_ι n (t, σ)

end VIRL5
