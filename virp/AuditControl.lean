import VIRP
-- POSITIVE CONTROL for Audit.lean: a theorem closed by `sorry` must print `sorryAx`, so a clean audit line means something.
theorem control_sorry : VIRP.HasType VIRP.Γ0 (VIRP.Tm.drop .truncated) := by sorry
#print axioms control_sorry
#print axioms VIRP.U_eq_F
-- 2026-11-23 THE IMPORTED CONTROL (term 3 of the axiom TRIPLE, harness/axiom_gate.py): an imported core constant, read from its
-- olean table, must print [Lean.trustCompiler]. The in-file control_sorry above tests the printer only (stale clean, h2c 11-23).
#print axioms Lean.reduceBool
