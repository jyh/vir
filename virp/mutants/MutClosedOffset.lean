import VIRP
open VIRP
-- MUTANT (must be RED): F_closed with the emit offset 12 instead of 24.
theorem F_closed_bad (σ : Store) : denote F env0 σ =
    Part.some (if (σ.wire.length : Int) ≥ 24 then
        (if rd32 σ.wire 0 = MAGIC ∧ σ.acl (rd32 σ.wire 4) (rd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (rd32 σ.wire 4)
         then (σ.dec (rd32 σ.wire 4), Label.emit 12) else (σ, Label.drop .unauthOrRate))
      else (σ, Label.drop .truncated)) := by
  simp only [denote, den, F, env0, Atom.eval, List.getElem?_cons_zero, List.getElem?_cons_succ]
  repeat' split
  all_goals simp_all [abort]
