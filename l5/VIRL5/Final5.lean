/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addenda 5–7): **Refine₅T, by the case split, and the two
  statements over ⟶₅.** Off the seven re-expressed modes the ⟶₅ entry is DEFLATE's own (`refine_lifted`); on them, each
  mode's case: READ and DECODE under (T), FIXLENS, SCOPY, BUILD, COPY, REP. Then `safety₅ : SafetyStmt₅` and
  `correct₅ : CorrectStmt₅` follow from Outer5T, with DEFLATE's proofs used as they stand.
-/
import VIRL5.RefineBuild5
import VIRL5.RefineRead5
import VIRL5.Outer5T

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- **The one per-mode obligation, discharged.** -/
theorem refine₅T : Refine₅T := by
  intro b om lit p σ f hb hw hs hi hT
  by_cases hx : Reex (f cMODE)
  · rcases hx with h | h | h | h | h | h | h
    · exact refine_read b om lit p σ f hb hw hs hi hT h
    · exact refine_fixlens b om lit p σ f hw hs hi h
    · exact refine_scopy b om lit p σ f hw hs hi h
    · exact refine_build b om lit p σ f hb hw hs hi h
    · exact refine_decode b om lit p σ f hb hw hs hi hT h
    · exact refine_copy b om lit p σ f hw hs hi h
    · exact refine_rep b om lit p σ f hw hs hi h
  · exact refine_lifted b om lit p σ f hb hw hs hi hx

/-- **SAFETY over ⟶₅:** from any input bytes, OUTMAX and flag, the ⟶₅ iteration reaches DONE or REJECT within DEFLATE's
  own bound. -/
theorem safety₅ : SafetyStmt₅ := safety₅_ofT refine₅T

/-- **CORRECTNESS over ⟶₅:** the ⟶₅ run ends exactly as DEFLATE's, so as S. -/
theorem correct₅ : CorrectStmt₅ := correct₅_ofT refine₅T

end VIRL5
