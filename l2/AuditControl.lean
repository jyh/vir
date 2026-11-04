import VIRL2
-- POSITIVE CONTROL for Audit.lean: a theorem closed by `sorry` must print `sorryAx`, so a clean audit line means something.
theorem control_sorry : VIRL2.Triple VIRL2.Assn.emp VIRL2.M3 (fun _ _ => True) := by sorry
#print axioms control_sorry
#print axioms VIRL2.M3_no_triple
