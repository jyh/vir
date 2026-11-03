/-
  O95 layer L2, Lean arm. M5 (inputs/L2-programs.md): K5 of inputs/L1-programs.md read in L2 — the SAME term, through ι
  (OBJECT-L2 §7). Its typing, its meaning for EVERY σ, and the triple `{P} K5 {v. ⌜v = 55⌝ ∗ P}` for EVERY P: the
  conservative-extension row, each from L1's own K5 facts and the three clauses, with no L1 definition edited.
-/
import VIRL2.Conservative
import VIRL2.Triples

namespace VIRL2
open VIRL1

/-- M5 = ι K5, byte-identical to L1's K5. -/
def M5 : Tm₂ := embE L1.K5

theorem M5_typed : HasType₂ [] [] M5 tint := conservative_typing L1.K5_typed

/-- ⟦K5⟧₂ σ = (55, σ) for EVERY σ. -/
theorem M5_meaning (σ : Store) : den₂ (M5, σ) = Part.some (ci 55, σ) := by
  rw [M5, conservative_den, L1.K5_meaning.2, Part.bind_some]; rfl

theorem embE_terminal {e : Tm₁} (h : (embE e).IsTerminal) : e.IsTerminal := by
  cases e with
  | ret => trivial
  | letOp o _ _ _ => exact nomatch (o : Empty)
  | _ => exact h

/-- `{P} K5 {v. ⌜v = 55⌝ ∗ P}` for EVERY P: the store is untouched, the frame clause in its strongest form. -/
theorem M5_triple (P : Assn) : Triple P M5 (fun v σ => v = ci 55 ∧ P σ) := by
  intro σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_⟩
  · obtain ⟨e', hs, rfl⟩ := steps₂_unemb hc
    rintro ⟨hnt, hns⟩
    rcases L1.safety₁ L1.K5_typed hs with ht | ⟨e'', hst⟩
    · cases e' with
      | ret a => exact hnt trivial
      | letOp o _ _ _ => exact nomatch (o : Empty)
      | _ => exact ht.elim
    · exact hns _ ((conservative_steps _).1 hst)
  · obtain ⟨e', hs, heq⟩ := steps₂_unemb hc
    injection heq with h₁ h₂; subst h₂
    obtain ⟨a₁, rfl, rfl⟩ := embE_eq_ret h₁.symm
    have hmem : L1.ci 55 ∈ den L1.K5 := by rw [L1.K5_meaning.2]; exact Part.mem_some _
    rw [soundness_steps hs] at hmem
    obtain ⟨a', hs', ha'⟩ := adequacy hmem
    cases hs' with
    | refl => exact ⟨ci 55, σ, by rw [embA_eval, ha']; rfl, hd, rfl, hwf, rfl, hP⟩
    | step h₁ _ => exact (Step.ret_irred h₁).elim

end VIRL2
