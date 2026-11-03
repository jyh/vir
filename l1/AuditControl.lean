import VIRL1
-- POSITIVE CONTROL for Audit.lean: a theorem closed by `sorry` must print `sorryAx`, so a clean audit line means something.
theorem control_sorry : VIRL1.HasType VIRL1.L1.E₁ [] VIRL1.L1.K2 VIRL1.L1.tbool := by sorry
#print axioms control_sorry
#print axioms VIRL1.L1.K2_diverges
