import VIRL1
-- POSITIVE CONTROL for Audit.lean: a theorem closed by `sorry` must print `sorryAx`, so a clean audit line means something.
theorem control_sorry : VIRL1.HasType VIRL1.L1.E₁ [] VIRL1.L1.K2 VIRL1.L1.tbool := by sorry
#print axioms control_sorry
#print axioms VIRL1.L1.K2_diverges
-- 2026-11-23 THE IMPORTED CONTROL (term 3 of the axiom TRIPLE, harness/axiom_gate.py): an imported core constant, read from its
-- olean table, must print [Lean.trustCompiler]. The in-file control_sorry above tests the printer only (stale clean, h2c 11-23).
#print axioms Lean.reduceBool
