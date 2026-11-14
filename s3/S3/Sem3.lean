/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 14): toward StepOk's S2 half. Every word state a word run reaches from
  an SRel-related start is itself SRel-related to some IR state, or is OVF (S2's `sim2_step` and the word machine's determinism).
-/
import S3.Need3
import VIRC.S2

namespace S3
open VIRC X86

theorem wn_terminal {T : Table} : ∀ {j : Nat} {W W₁ : WSt × WMem}, WN T j W W₁ → (W.1 = .ovf ∨ W.1 = .fault) → W₁ = W := by
  intro j W W₁ h hterm
  cases h with
  | refl => rfl
  | step hs _ =>
    obtain ⟨w, m⟩ := W
    rcases hterm with h | h <;> (simp only at h; subst h; simp [stepW] at hs)

/-- **srel_reach.** Along a word run from a state S2 relates to an IR state, every reached word state is related to some IR state,
    or the word machine stopped at OVF or FAULT. -/
theorem srel_reach {T : Table} {lay : Int → W} {τfin : VIRL2.Ty₂} (hT : T.length < 2 ^ 64) :
    ∀ {k : Nat} {W W₁ : WSt × WMem}, WN T k W W₁ → ∀ {I : St × VIRL2.Store}, SRel T lay τfin I W →
      (∃ I₁, SRel T lay τfin I₁ W₁) ∨ (W₁.1 = .ovf ∨ W₁.1 = .fault) := by
  intro k W W₁ h
  induction h with
  | refl W => intro I hI; exact .inl ⟨I, hI⟩
  | step hs hrest ih =>
    intro I hI
    obtain ⟨st, σ⟩ := I
    cases st with
    | done v => cases hI with | done _ => simp [stepW] at hs
    | run c ρ fr =>
      rcases sim2_step hT hI with ⟨_, W₂, hs₂, hterm⟩ | ⟨I', _, W₂, hs₂, hrel⟩
      · rw [hs] at hs₂; cases hs₂
        rw [wn_terminal hrest hterm.symm]; exact .inr hterm.symm
      · rw [hs] at hs₂; cases hs₂
        rcases hrel with hrel | hovf
        · exact ih hrel
        · rw [wn_terminal hrest (.inl hovf)]; exact .inr (.inl hovf)

end S3
