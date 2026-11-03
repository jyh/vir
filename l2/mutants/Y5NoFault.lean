/-
  O95 amend-16 Y5, RED BACKWARDS (STATUS-vir row 125). The MUTANT restores OBJECT-L2 §5's literal reading: `rt_triple`'s
  proof, word for word, against the NO-FAULT `Triple` (no index-fault exception). If Y5's exception carries weight, this file
  must FAIL, and fail exactly in the branch where progress returns an IndexFault — the one line the mutant cannot close.
  Its log is `logs/mutant-002.log`; the build there must read EXIT ≠ 0 with one error, at the IndexFault branch.
  (The statement is ALSO refuted outright in VIRL2: `semantic_typing_literal_false`, M3.)
-/
import VIRL2

namespace VIRL2
open VIRL1

theorem rt_triple_nofault {Ω : List Int} {e : Tm₂} {τ : Ty₂} (ht : RT [] [] Ω e τ) : Triple (OwnAll Ω) e (Y5Post τ) := by
  intro σ σf ho hd hwf
  refine ⟨fun ⟨e', σc⟩ hc => ?_, fun a σ' hc => (rt_triple ht σ σf ho hd hwf).2 a σ' hc⟩
  obtain ⟨Ω', σq', ht', ho', -, hσ', hwf'⟩ := steps_rt hc ht ho hd hwf rfl
  dsimp only at ht' hσ'
  subst hσ'
  rintro ⟨hnt, hns⟩
  rcases progress_rt ht' hwf' (fun p hp => ho'.live hp σf) with h | ⟨c', hs⟩ | h
  · exact hnt h
  · exact hns c' hs
  · exact h

end VIRL2
