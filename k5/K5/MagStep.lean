/-
  O95, K5-2b: `Mag_step`'s infrastructure (DECLARATIONS-K5.md Addenda 4–5), and its first mode.
  Route, per mode: the mode's explicit step (Safety's `safe_*` or Step.lean's `<mode>_step` through `stepS_of_mode`) pins the
  store `stepS` returns; a world over one store is unique on its region (`world_uniq`), so the cells after the step are the
  explicit ones; `Mag` reads only region cells (`Mag_congr`), so `Mag` after the step is `Mag` of the explicit cell function.
-/
import K5.InRange

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

/-- Two worlds over the same store and base agree on the region. -/
theorem world_uniq {σ : Store} {p : Int} {L : Nat} {f g : Int → Int} (hf : World σ p L f) (hg : World σ p L g)
    (c : Int) (h0 : 0 ≤ c) (hL : c < L) : f c = g c := by
  have a := hf.cell c h0 hL
  have b := hg.cell c h0 hL
  rw [a] at b
  exact Option.some.inj b

/-- `Mag` reads only cells of the region. -/
theorem Mag_congr {n om : Nat} {f g : Int → Int} (h : ∀ c : Int, 0 ≤ c → c < (L0 n om : Int) → f c = g c)
    (hg : Mag n om g) : Mag n om f := by
  have hL0 : (L0 n om : Int) = n + om + 3626 := by unfold L0; push_cast; ring
  have e : ∀ c : Int, 0 ≤ c → c < n + om + 3626 → f c = g c := fun c a b => h c a (by rw [hL0]; exact b)
  have eM := e cMODE (by decide) (by unfold cMODE; omega)
  have eR := e cRET (by decide) (by unfold cRET; omega)
  have eem : em f = em g := by simp only [em, eM, eR]
  have eP := e cPEND (by decide) (by unfold cPEND; omega)
  have eD := e cDIST (by decide) (by unfold cDIST; omega)
  have eC := e cCODE (by decide) (by unfold cCODE; omega)
  have eL := e cLEFT (by decide) (by unfold cLEFT; omega)
  have eRs := e cREST (by decide) (by unfold cREST; omega)
  have eT := e cTOTAL (by decide) (by unfold cTOTAL; omega)
  have eI := e cINDEX (by decide) (by unfold cINDEX; omega)
  have eH := e cPHASE (by decide) (by unfold cPHASE; omega)
  have eX0 := e (X0 n om) (by unfold X0; omega) (by unfold X0; omega)
  have eX1 := e (X0 n om + 1) (by unfold X0; omega) (by unfold X0; omega)
  have eX3 := e (X0 n om + 3) (by unfold X0; omega) (by unfold X0; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1; rw [eP]; exact hg.p1 (by rwa [← eem])
  · intro h1; rw [eP]; exact hg.p2 (by rwa [← eem])
  · intro h1; rw [eP]; exact hg.p3 (by rw [← eem, ← eM, ← eX3]; exact h1)
  · intro h1; rw [eP]; exact hg.p4 (by rwa [← eem])
  · intro h1; rw [eD]; exact hg.d1 (by rwa [← eem])
  · intro h1; rw [eX1, eX0]; exact hg.c1 (by rwa [← eM])
  · intro h1 h2; rw [eC, eI]; exact hg.b1 (by rwa [← eM]) (by rwa [← eH])
  · intro h1 h2; rw [eL, eRs, eT, eI]; exact hg.b2 (by rwa [← eM]) (by rwa [← eH])
  · intro t l a1 a2 a3 a4
    rw [e _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)]
    exact hg.f1 t l a1 a2 a3 a4

/-- The form every mode's case takes: the step's store is the explicit one, so `Mag` after it is `Mag` of the explicit cells. -/
theorem Mag_of_explicit {b : Array Nat} {om : Nat} {σ σ' σe : Store} {p : Int} {f' g : Int → Int}
    (hS : stepS p σ = some σ') (hSe : stepS p σ = some σe) (hw' : World σ' p (L0 b.size om) f')
    (hwe : World σe p (L0 b.size om) g) (hg : Mag b.size om g) : Mag b.size om f' := by
  rw [hS] at hSe
  cases hSe
  exact Mag_congr (fun c a h => world_uniq hw' hwe c a (by exact_mod_cast h)) hg

/-- **SLEN** (the step that MAKES P1): pend := acc with acc < 65536, then a READ returning to SNLEN. -/
theorem Mag_step_slen {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mSLEN)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  obtain ⟨hSe, hwe, -, -⟩ := safe_slen (b := b) (om := om) (lit := lit) hw (by unfold L0; omega) hi.1 hm
  refine Mag_of_explicit hS hSe hw' hwe ?_
  have ha := acc_rng hi (by rw [hm]; decide)
  have hacc := hi.2.ret (by rw [hm]; decide)
  have hk : kcap mSLEN = 65536 := by simp [kcap, mSLEN, mHDRB, mHDRD]
  set g := reqF (Function.update f 5 (f cACC)) 16 9 with hgd
  have u : ∀ c : Int, c ≠ 0 → c ≠ 5 → c ≠ 2068 → c ≠ 2069 → c ≠ 2070 → c ≠ 2071 → g c = f c := by
    intro c a0 a5 a1 a2 a3 a4
    simp [hgd, reqF, Function.update_apply, a0, a5, a1, a2, a3, a4]
  have gM : g cMODE = mREAD := by simp [hgd, reqF, cMODE, mREAD]
  have gR : g cRET = mSNLEN := by simp [hgd, reqF, cRET, mSNLEN]
  have gP : g cPEND = f cACC := by simp [hgd, reqF, cPEND]
  have gem : em g = mSNLEN := by simp [em, gM, gR]
  have hX : 2080 ≤ X0 b.size om := by unfold X0; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rw [gP]; rw [hm, hk] at hacc; omega
  · intro h; rw [gem] at h; exact absurd h (by decide)
  · intro h; rw [gem] at h; rcases h with h | h | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [gM] at h; exact absurd h (by decide)
  · intro h; rw [gem] at h; exact absurd h (by decide)
  · intro h; rw [gem] at h; exact absurd h (by decide)
  · intro h; rw [gM] at h; exact absurd h (by decide)
  · intro h; rw [gM] at h; exact absurd h (by decide)
  · intro h; rw [gM] at h; exact absurd h (by decide)
  · intro t l a1 a2 a3 a4
    rw [u _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)
      (by unfold tbase LB0; omega) (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)]
    exact hg.f1 t l a1 a2 a3 a4

end K5
