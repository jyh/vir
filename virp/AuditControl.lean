import VIRP
-- POSITIVE CONTROL for Audit.lean: a theorem closed by `sorry` must print `sorryAx`, so a clean audit line means something.
theorem control_sorry : VIRP.HasType VIRP.Γ0 (VIRP.Tm.drop .truncated) := by sorry
#print axioms control_sorry
#print axioms VIRP.U_eq_F
