import VIRDeflate
open VIRDeflate Run in
-- MUTANT: the one-literal stream expected to give "b" (98) instead of the manifest's "a" (97). Must be RED.
theorem mutant_wrong_byte : acceptsWith (inflate i_fixed_one_literal 65536) #[98] = true := by decide +kernel
