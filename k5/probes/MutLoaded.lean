import K5.DeflateLoaded
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5
-- mutant 1: the placement bound dropped; the proof must fail at Placed (one error expected, line 13)
theorem mut_noplace {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hp0 : 0 ≤ p) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) : Layout σ scaleLay := by
  have hS := reach_shape hb hn32 hom32 k σ h
  have hpl : Placed σ := by
    intro q n hq
    rw [hS.reg] at hq
    obtain ⟨rfl, rfl⟩ := lookup_single hq
    exact ⟨hp0, by omega⟩
  exact (loader_ok hS.wf hpl hS.cells).1
-- mutant 2: alloc allowed in the term predicate; a store-shape claim without tmOk must fail (one error expected)
theorem mut_alloc {c c' : Config} (hs : Step₂ c c') (hi : Tm.HeadInR c.1) {R₀} (hS : Shape R₀ c.2) : Shape R₀ c'.2 :=
  (step_ok hs (by assumption) hi hS).2
