import VIRDeflate.Step
open VIRDeflate VIRDeflate.Step VIRL2
example : retInt? (run₂ 1000 (bitProg 200 3, Store.empty)).1 = some 1 := by decide +kernel
example : retInt? (run₂ 1000 (bitProg 200 0, Store.empty)).1 = some 0 := by decide +kernel
