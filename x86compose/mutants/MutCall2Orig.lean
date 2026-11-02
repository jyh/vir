import X86Compose
/-! ## TWO CALLS at the meaning (STATUS-vir row 85): paris's `sim_two` (spike/o95-router 52772fa) composed with ⟦F⟧ -/
-- MUTANT (must be RED): call 2 on the ORIGINAL store, not the one call 1 returned.
namespace X86ComposeMut2
open X86Compose
open X86 Router.Refines Router.Layout

/-- F_closed's right-hand side as a function. -/
def R1 (σ : VIRP.Store) : VIRP.Store × VIRP.Label :=
  if (σ.wire.length : Int) ≥ 24 then
    (if VIRP.rd32 σ.wire 0 = VIRP.MAGIC ∧ σ.acl (VIRP.rd32 σ.wire 4) (VIRP.rd32 σ.wire 8) = true ∧
        1 ≤ σ.bucket (VIRP.rd32 σ.wire 4)
     then (σ.dec (VIRP.rd32 σ.wire 4), VIRP.Label.emit 24) else (σ, VIRP.Label.drop .unauthOrRate))
  else (σ, VIRP.Label.drop .truncated)

theorem denote_R1 (σ : VIRP.Store) : VIRP.denote VIRP.F VIRP.env0 σ = Part.some (R1 σ) := VIRP.F_closed σ

theorem Fc_R1 (σ : VIRP.Store) : Router.Sim.Fc (toV σ) = (toV (R1 σ).1, lab (R1 σ).2) := Fc_faithful σ

/-- **Two calls at the meaning:** call 1 is ⟦F⟧ σ; a caller that writes ONLY the next buffer and re-enters (sim_two's
premises, all about the placement and the caller's writes, none about the program) gets call 2 = ⟦F⟧ on the store call 1
RETURNED, with the new wire. -/
theorem backend_two (σ : VIRP.Store) (s1 : Cpu) (hR : Rel σ.wire σ.bucket σ.acl s1) :
    ∃ n1, (runP Router.repaired n1 s1).stopped = true ∧
      Router.Sim.exitLabel (runP Router.repaired n1 s1) = some (lab (R1 σ).2) ∧
      ∀ (s2 : Cpu) (w2 : List Int), Live s2 → s2.rip = 0x1000 → s2.regs.get .rdx = s1.regs.get .rdx →
        Placement (s1.regs.get .rdx) (s2.regs.get .rdi) w2.length → w2.length = (s2.regs.get .rsi).toNat →
        (∀ i, (h : i < w2.length) → w2[i] = ((s2.mem.read (s2.regs.get .rdi + BitVec.ofNat 64 i)).toNat : Int)) →
        AgreeOutside (Region (s2.regs.get .rdi) w2.length) (runP Router.repaired n1 s1).mem s2.mem →
        ∃ n2, (runP Router.repaired n2 s2).stopped = true ∧
          Router.Sim.exitLabel (runP Router.repaired n2 s2) = some (lab (R1 { σ with wire := w2 }).2) ∧
          Router.Sim.Post (toV (R1 { σ with wire := w2 }).1) s2 (runP Router.repaired n2 s2) := by
  obtain ⟨n1, h1, h2, h3⟩ := Router.Sim.sim_two (toV σ) s1 hR
  rw [Fc_R1] at h2
  refine ⟨n1, h1, h2, fun s2 w2 a b c d e f g => ?_⟩
  have := h3 s2 w2 a b c d e f g
  simp only [Fc_R1] at this
  have hw : ({ (toV (R1 σ).1) with wire := w2 } : Router.Sim.VStore) = toV { (R1 σ).1 with wire := w2 } := rfl
  rw [hw, Fc_R1] at this
  exact this

end X86ComposeMut2
