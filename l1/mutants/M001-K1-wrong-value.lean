import VIRL1
-- MUTANT (must be RED): K1's meaning claimed as 121. If this builds, K1_meaning's value is not load-bearing.
open VIRL1 VIRL1.L1
theorem K1_wrong : den K1 = Part.some (ci 121) := (trace_den (n := 200) ⟨_, rfl, rfl⟩).2
