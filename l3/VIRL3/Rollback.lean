/-
  O95 layer L3, Lean arm. R3 (G4 (a)), read under errata L3-E1: for every store whose world satisfies the router's layout
  (here only what the proof needs: sender and topic in [0, 4)), `⟦U_tx⟧₂ σ = ⟦F⟧₂ σ`. Both runs are computed symbolically
  (`symrun`, VIRL3/Sym.lean) on each branch — short frame · wrong magic · no token · no ACL bit (U_tx's rollback) · emit —
  and agree; the step function's soundness carries the run equality to the meanings.
-/
import VIRL3.Sym

namespace VIRL3
open VIRL1 VIRL2

/-- R3's run equality on the short path (LEN < 24): both exit with code 1. -/
theorem R3_run_short {σ p f} (hw : World σ p f) (hn : ¬ 24 ≤ f 0) :
    run₂ 80 (closeAt p U_tx, σ) = run₂ 80 (closeAt p F, σ) := by
  have h0 := hw.cell 0 (by decide) (by decide)
  symrun [hw.cell, hw.reg, h0, hn]

set_option maxHeartbeats 4000000 in
/-- R3's run equality on the long path, every branch: magic, tokens, ACL bit. -/
theorem R3_run_long {σ p f} (hw : World σ p f) (hn : 24 ≤ f 0)
    (hs0 : 0 ≤ Sv f) (hs4 : Sv f < 4) (ht0 : 0 ≤ Tv f) (ht4 : Tv f < 4) :
    run₂ 80 (closeAt p U_tx, σ) = run₂ 80 (closeAt p F, σ) := by
  have h0 := hw.cell 0 (by decide) (by decide)
  have hacl : 0 ≤ 67 + (Sv f * 4 + Tv f) ∧ 67 + (Sv f * 4 + Tv f) < 87 := by omega
  have hbk : 0 ≤ 83 + Sv f ∧ 83 + Sv f < 87 := by omega
  have hne : p + (67 + (Sv f * 4 + Tv f)) ≠ p + (83 + Sv f) := by omega
  have hbv := hw.cell (83 + Sv f) hbk.1 hbk.2
  simp only [Sv, Tv] at hacl hbk hne hbv
  by_cases hm : f 3 + (256 * f 4 + (65536 * f 5 + 16777216 * f 6)) = 1297303345
  · by_cases hk : 0 < f (83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))))
    · by_cases ha : f (67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 +
          (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14))))) = 1
      · symrun [hw.cell, hw.reg, h0, hn, hm, hk, ha, hacl, hbk, hne]
      · symrun [hw.cell, hw.reg, h0, hn, hm, hk, ha, hacl, hbk, hne, insert_self_of_lookup hbv]
    · symrun [hw.cell, hw.reg, h0, hn, hm, hk, hacl, hbk, hne]
  · symrun [hw.cell, hw.reg, h0, hn, hm, hacl, hbk, hne]

/-- R3 (OBJECT-L3 §3.2 under L3-E1): ⟦U_tx⟧₂ = ⟦F⟧₂ on every store whose world carries an in-range sender and topic. -/
theorem R3 {σ : Store} {p : Int} {f : Int → Int} (hw : World σ p f)
    (hs0 : 0 ≤ Sv f) (hs4 : Sv f < 4) (ht0 : 0 ≤ Tv f) (ht4 : Tv f < 4) :
    den₂ (closeAt p U_tx, σ) = den₂ (closeAt p F, σ) := by
  rw [soundness₂_steps (run₂_steps 80 (closeAt p U_tx, σ)), soundness₂_steps (run₂_steps 80 (closeAt p F, σ))]
  by_cases hn : 24 ≤ f 0
  · rw [R3_run_long hw hn hs0 hs4 ht0 ht4]
  · rw [R3_run_short hw hn]

end VIRL3
