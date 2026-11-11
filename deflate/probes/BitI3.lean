import VIRDeflate.Step
open VIRDeflate VIRDeflate.Step VIRL2
theorem probe_i3 : ∀ b : Fin 256, retInt? (run₂ 1000 (bitProg b.val 3, Store.empty)).1 = some (bitAt (b.val : Int) 3) := by decide +kernel
