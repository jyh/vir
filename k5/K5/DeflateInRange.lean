/-
  O95, **K5-2 `deflate_inrange`** (DECLARATIONS-K5.md K5-2, with Addenda 3–5's `Mag`): for bytes < 256 and n, OUTMAX < 2³², every
  world DEFLATE's iteration reaches from its initial store carries `Inv ∧ Mag` (Safety's `stepSafe_of safeI_build` keeps `Inv`,
  `Mag_step` keeps `Mag`, DONE/REJECT are fixed points by `stepS_fixed`), so its next step term is in range (`step_inrange`).
-/
import K5.MagAll
import VIRDeflate.Correct

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

/-- `Inv ∧ Mag` on every world the iteration reaches. -/
theorem reach_inv {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ0 σ : Store), (∃ f, World σ0 p (L0 b.size om) f ∧ Inv b om lit f ∧ Mag b.size om f) →
      iterS p k σ0 = some σ → ∃ f, World σ p (L0 b.size om) f ∧ Inv b om lit f ∧ Mag b.size om f
  | 0, σ0, σ, h, hi => by simp only [iterS, Option.some.injEq] at hi; subst hi; exact h
  | k + 1, σ0, σ, ⟨f, hw, hI, hg⟩, hi => by
    simp only [iterS] at hi
    cases hS : stepS p σ0 with
    | none => rw [hS] at hi; cases hi
    | some σ1 =>
      rw [hS] at hi
      refine reach_inv hb k σ1 σ ?_ hi
      by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
      · have := stepS_fixed hw (by unfold L0; omega) ht
        rw [hS] at this; cases this
        exact ⟨f, hw, hI, hg⟩
      · push_neg at ht
        obtain ⟨σ', f', hS', hw', hI', -⟩ := stepSafe_of safeI_build b om lit p σ0 f hb hw hI ht.1 ht.2
        rw [hS] at hS'; cases hS'
        exact ⟨f', hw', hI', Mag_step hb hw hI hg ht.1 ht.2 hS hw'⟩

/-- **K5-2.** For every byte string (bytes < 256), n, OUTMAX < 2³², either reading, and every world the iteration reaches,
the step term's next-evaluated atoms are in range at every configuration of its run. -/
theorem deflate_inrange {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) : SrcInRange (closeAt p stepT, σ) := by
  obtain ⟨f, hw, hI, hg⟩ := reach_inv (om := om) (lit := lit) hb k _ σ
    ⟨_, initStore_world b om lit p, Inv_init b om lit, Mag_init b om lit⟩ h
  exact step_inrange hb hn32 hom32 hw hI hg

end K5
