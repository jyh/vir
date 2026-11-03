import VIRL1
-- MUTANT (must be RED): K2 claimed to have a value. The kernel cannot reduce `run` to a `ret`, so this must not build.
open VIRL1 VIRL1.L1
theorem K2_wrong : ∃ a, run 200 K2 = .ret a := ⟨_, rfl⟩
