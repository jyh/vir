/-
  O95 amend-11 V4 (and V5's machine reading), STATUS-vir row 82. paris's one-call backend theorem `sim_one`
  (x86lean paris/o95-layout 2af56c7) states its conclusion about `Fc`, a RESTATEMENT of vir's `F_closed` right-hand side.
  Here the kernel checks the restatement: `Fc` of the store IS ⟦F⟧'s result, so the backend theorem speaks of the meaning
  itself, ⟦F⟧ = `denote F env0`. The ONLY premise is the layout relation R (paris's `Rel`).
-/
import VIRP.Router
import Router.Sim

namespace X86Compose
open X86 Router.Refines Router.Layout

/-- vir's store as the spike's (the same three fields). -/
def toV (σ : VIRP.Store) : Router.Sim.VStore := ⟨σ.wire, σ.bucket, σ.acl⟩

def lab : VIRP.Label → Router.Sim.Label
  | .emit o => .emit o
  | .drop .truncated => .drop .truncated
  | .drop .unauthOrRate => .drop .unauthOrRate

/-- The restatement is faithful: the spike's `Fc` on vir's store is ⟦F⟧'s closed form, componentwise. -/
theorem Fc_faithful (σ : VIRP.Store) :
    Router.Sim.Fc (toV σ) =
      (toV (if (σ.wire.length : Int) ≥ 24 then
          (if VIRP.rd32 σ.wire 0 = VIRP.MAGIC ∧ σ.acl (VIRP.rd32 σ.wire 4) (VIRP.rd32 σ.wire 8) = true ∧
              1 ≤ σ.bucket (VIRP.rd32 σ.wire 4)
           then (σ.dec (VIRP.rd32 σ.wire 4), VIRP.Label.emit 24) else (σ, VIRP.Label.drop .unauthOrRate))
         else (σ, VIRP.Label.drop .truncated)).1,
       lab (if (σ.wire.length : Int) ≥ 24 then
          (if VIRP.rd32 σ.wire 0 = VIRP.MAGIC ∧ σ.acl (VIRP.rd32 σ.wire 4) (VIRP.rd32 σ.wire 8) = true ∧
              1 ≤ σ.bucket (VIRP.rd32 σ.wire 4)
           then (σ.dec (VIRP.rd32 σ.wire 4), VIRP.Label.emit 24) else (σ, VIRP.Label.drop .unauthOrRate))
         else (σ, VIRP.Label.drop .truncated)).2) := by
  simp only [Router.Sim.Fc, toV, Router.Sim.vrd32, VIRP.rd32, Router.Sim.MAGIC, VIRP.MAGIC]
  split_ifs <;> rfl

/-- **V4, at the meaning:** for every store σ and every machine state s related to it by the layout relation, ⟦F⟧ σ is
defined, and the repaired x86 router run from s STOPS at the exit whose label is ⟦F⟧'s, in a final memory related to ⟦F⟧'s
store. The ONLY premise is R. -/
theorem backend_F (σ : VIRP.Store) (s : Cpu) (hR : Rel σ.wire σ.bucket σ.acl s) :
    ∃ r, VIRP.denote VIRP.F VIRP.env0 σ = Part.some r ∧
      ∃ n, (runP Router.repaired n s).stopped = true ∧
        Router.Sim.exitLabel (runP Router.repaired n s) = some (lab r.2) ∧
        Router.Sim.Post (toV r.1) s (runP Router.repaired n s) := by
  refine ⟨_, VIRP.F_closed σ, ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := Router.Sim.sim_one (toV σ) s hR
  rw [Fc_faithful] at h2 h3
  exact ⟨n, h1, h2, h3⟩

end X86Compose

/-! ## TWO CALLS at the meaning (STATUS-vir row 85): paris's `sim_two` (spike/o95-router 52772fa) composed with ⟦F⟧ -/
namespace X86Compose
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
          Router.Sim.exitLabel (runP Router.repaired n2 s2) = some (lab (R1 { (R1 σ).1 with wire := w2 }).2) ∧
          Router.Sim.Post (toV (R1 { (R1 σ).1 with wire := w2 }).1) s2 (runP Router.repaired n2 s2) := by
  obtain ⟨n1, h1, h2, h3⟩ := Router.Sim.sim_two (toV σ) s1 hR
  rw [Fc_R1] at h2
  refine ⟨n1, h1, h2, fun s2 w2 a b c d e f g => ?_⟩
  have := h3 s2 w2 a b c d e f g
  simp only [Fc_R1] at this
  have hw : ({ (toV (R1 σ).1) with wire := w2 } : Router.Sim.VStore) = toV { (R1 σ).1 with wire := w2 } := rfl
  rw [hw, Fc_R1] at this
  exact this

end X86Compose
