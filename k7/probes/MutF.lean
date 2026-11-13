import K7
open VIRL1 VIRL2 VIRC VIRL3
-- mutants: decide must REFUSE false facts about F (errors expected at lines 5 and 7)
set_option maxRecDepth 100000 in
theorem mut_ok2 : Tm.ok2 F = false := by decide
set_option maxRecDepth 100000 in
theorem mut_T : (lower2T [tcap] F []).2.length < 2 := by decide
