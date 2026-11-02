import VIRP
open VIRP
-- MUTANT (must be RED): the 0-token store EMITS.
theorem exit_rate_bad : denote F env0 (store (frame magicLE 100) true 0)
    = Part.some ((store (frame magicLE 100) true 0).dec 0, .emit 24) := by
  rw [F_closed]; simp [store, frame, magicLE, rd32, MAGIC]
