import VIRP
open VIRP
-- MUTANT (must be RED): F that RETURNS without consuming the fresh token st' (returns the slice twice) — linearity.
def Fbad : Tm :=
  .guard (.ge (.len (.var 0)) (.lit 24))
    (.readU32 (.var 0) 0 (.readU32 (.var 1) 4 (.readU32 (.var 2) 8
      (.guard (.and (.eq (.var 2) .magic) (.and (.canAccess (.var 1) (.var 0)) (.hasTokens (.var 4) (.var 1))))
        (.letLinDec (.var 4) (.var 1) (.advance (.var 4) 24 (.ret (.sl 0) (.var 0))))
        (.drop .unauthOrRate)))))
    (.drop .truncated)
theorem Fbad_typed : HasType Γ0 Fbad := by
  repeat' first | exact Use.var rfl | decide | constructor | rfl
