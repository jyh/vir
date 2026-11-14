/-
  O95 layer L5, Lean arm (STATUS 319, LV8 (b); LV8-MAP Addendum 9): EVERY L2 `Triple` carries to a `Triple₅` of its embedding ιE.
  Generic: it names no program and no routine. It uses CE both ways (ce_fwd, and ce_bwd through steps₅_ι_bwd). An embedded
  configuration never reaches `retK`, so the third clause is vacuous and nothing is handed back.
-/
import VIRL5.Embed5

namespace VIRL5
open VIRL1 VIRL2

/-- An embedded configuration that faults under ⟶₅ faults under ⟶₂: a ⟶₂ step would embed (ce_fwd), and `ret` embeds to `ret`. -/
theorem faults₅_ι {e : Tm₂} {σ : Store} (h : Faults₅ (ιE e, σ)) : Faults (e, σ) := by
  refine ⟨fun ht => h.1 ?_, fun c hs => h.2 _ (ce_fwd hs)⟩
  cases e <;> simp_all [ιE, Tm₅.IsTerminal, Tm.IsTerminal]

/-- **triple_ι.** `{P} e {v. Q v}` over ⟶₂ gives `{P} ιE e {v, qs. ∃ w, v = ιA w ∧ qs = [] ∧ Q w}` over ⟶₅. -/
theorem triple_ι {P : Assn} {e : Tm₂} {Q : Atom₂ → Assn} (h : Triple P e Q) :
    Triple₅ P (ιE e) (fun v qs σ => ∃ w, v = ιA w ∧ qs = [] ∧ Q w σ) := by
  intro σ σf hP hd hwf
  obtain ⟨hsafe, hpost⟩ := h σ σf hP hd hwf
  refine ⟨fun c hc hf => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · obtain ⟨e', σ', hs', rfl⟩ := steps₅_ι_bwd hc e _ rfl
    exact hsafe _ hs' (faults₅_ι hf)
  · obtain ⟨e', σ'', hs', heq⟩ := steps₅_ι_bwd hc e _ rfl
    cases e' <;> simp [ιE] at heq
    rename_i a₀
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨v, σq, hv, hq, rfl, hw, hQ⟩ := hpost a₀ _ hs'
    exact ⟨ιA v, σq, by rw [eval_ι, hv]; rfl, hq, rfl, hw, v, rfl, rfl, hQ⟩
  · obtain ⟨e', σ'', hs', heq⟩ := steps₅_ι_bwd hc e _ rfl
    cases e' <;> simp [ιE] at heq

end VIRL5
