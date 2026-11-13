import K5.DeflateNoOvf
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step
-- mutant: the evaluator must REFUSE a false per-program fact (line 5 is the one expected error)
set_option maxRecDepth 100000 in
theorem mut_ok2 : Tm.ok2 stepT = false := by decide
-- mutant: a table bound one bit too small for a NON-trivial table must also be refused if the table has ≥ 2 entries
set_option maxRecDepth 100000 in
theorem mut_T : (lower2T [tcap] stepT []).2.length < 2 := by decide
