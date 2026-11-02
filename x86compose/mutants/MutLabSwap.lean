/-
  O95 amend-11 V4 (and V5's machine reading), STATUS-vir row 82. paris's one-call backend theorem `sim_one`
  (x86lean paris/o95-layout 2af56c7) states its conclusion about `Fc`, a RESTATEMENT of vir's `F_closed` right-hand side.
  Here the kernel checks the restatement: `Fc` of the store IS ⟦F⟧'s result, so the backend theorem speaks of the meaning
  itself, ⟦F⟧ = `denote F env0`. The ONLY premise is the layout relation R (paris's `Rel`).
-/
import VIRP.Router
import Router.Sim

-- MUTANT (must be RED): the label map swaps the two drop codes.
namespace X86ComposeMut
open X86 Router.Refines Router.Layout

/-- vir's store as the spike's (the same three fields). -/
def toV (σ : VIRP.Store) : Router.Sim.VStore := ⟨σ.wire, σ.bucket, σ.acl⟩

def lab : VIRP.Label → Router.Sim.Label
  | .emit o => .emit o
  | .drop .truncated => .drop .unauthOrRate
  | .drop .unauthOrRate => .drop .truncated

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

end X86ComposeMut
