import K5.DeflateInRange
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

set_option maxRecDepth 100000 in
theorem p_wf : Tm.wfB [tcap].length stepT = true := by decide
set_option maxRecDepth 100000 in
theorem p_fn : Tm.fnOk stepT = true := by decide
set_option maxRecDepth 100000 in
theorem p_ok : Tm.ok2 stepT = true := by decide
set_option maxRecDepth 100000 in
theorem p_T : (lower2T [tcap] stepT []).2.length < 2 ^ 64 := by decide
theorem p_inst (p : Int) : instL 0 [.const (.cap p)] stepT = closeAt p stepT := rfl
#print axioms p_wf
#print axioms p_T
