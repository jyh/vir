/-
  O95 VIR program, Lean arm: THE ROUTER FRAGMENT through the six steps. I3's U (I2's specs composed) and A.3's fused F as
  deep terms in the context [b0 : slice, bucket_st : tok] (index 0 = b0); both TYPED (tokens linear, buffers affine);
  ⟦F⟧ TOTAL (a theorem, no fuel); and I4 at the new meaning: ⟦U⟧ = ⟦F⟧ for EVERY store, drops aborting.
-/
import VIRP.Safety

namespace VIRP

/-- The context and the environment of a call: the frame buffer at offset 0, and the bucket capability. -/
def Γ0 : Ctx := [some .slice, some .tok]
def env0 : List Val := [.sl 0, .tok]

/-- I3's U: parse_header ; check_rate_limit ; verify_acl ; emit_payload (I2), composed. -/
def U : Tm :=
  .guard (.ge (.len (.var 0)) (.lit 24))
    (.readU32 (.var 0) 0                                 -- magic, b0, st
      (.guard (.eq (.var 0) .magic)
        (.readU32 (.var 1) 4                             -- sender, magic, b0, st
          (.readU32 (.var 2) 8                           -- topic, sender, magic, b0, st
            (.advance (.var 3) 12                        -- s, topic, sender, magic, (b0), st
              (.guard (.hasTokens (.var 5) (.var 2))
                (.letLinDec (.var 5) (.var 2)            -- st2, s, topic, sender, magic, (b0), (st)
                  (.guard (.canAccess (.var 3) (.var 2))
                    (.advance (.var 1) 12                -- payload, st2, (s), ...
                      (.ret (.var 1) (.var 0)))
                    (.drop .unauthOrRate)))
                (.drop .unauthOrRate)))))
        (.drop .unauthOrRate)))
    (.drop .truncated)

/-- A.3's fused single-pass term F. -/
def F : Tm :=
  .guard (.ge (.len (.var 0)) (.lit 24))
    (.readU32 (.var 0) 0                                 -- magic, b0, st
      (.readU32 (.var 1) 4                               -- sender, magic, b0, st
        (.readU32 (.var 2) 8                             -- topic, sender, magic, b0, st
          (.guard (.and (.eq (.var 2) .magic) (.and (.canAccess (.var 1) (.var 0)) (.hasTokens (.var 4) (.var 1))))
            (.letLinDec (.var 4) (.var 1)                -- st', topic, sender, magic, b0, (st)
              (.advance (.var 4) 24                      -- payload_slice, st', ..., (b0)
                (.ret (.var 1) (.var 0))))
            (.drop .unauthOrRate)))))
    (.drop .truncated)

/-! ## Step 2: both programs are well-formed -/
theorem U_wf : U.wf 2 := by simp [U, Tm.wf, Atom.wf]
theorem F_wf : F.wf 2 := by simp [F, Tm.wf, Atom.wf]

/-! ## Step 4: both programs are well-typed -/
theorem U_typed : HasType Γ0 U := by
  repeat' first | exact Use.var rfl | decide | constructor | rfl
theorem F_typed : HasType Γ0 F := by
  repeat' first | exact Use.var rfl | decide | constructor | rfl

theorem env0_ok : EnvOK Γ0 env0 := (EnvOK.nil.cons .tok).cons .sl

/-! ## Step 6: the meaning is total (no fuel, no fixpoint: amend-11 V6) -/
theorem F_total (σ : Store) : (denote F env0 σ).Dom := by
  simpa [denote] using F_typed.den_dom env0_ok σ
theorem U_total (σ : Store) : (denote U env0 σ).Dom := by
  simpa [denote] using U_typed.den_dom env0_ok σ

/-! ## I4 at the new meaning: U and F denote the same function of the store -/
theorem U_eq_F (σ : Store) : denote U env0 σ = denote F env0 σ := by
  simp only [denote, den, U, F, env0, Atom.eval, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hacl : ∀ x, (σ.dec x).acl = σ.acl := fun _ => rfl
  simp only [hacl]
  repeat' split
  all_goals simp_all [abort]

end VIRP
