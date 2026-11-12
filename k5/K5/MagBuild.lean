/-
  O95, K5-2b: `Mag_step` for BUILD (DECLARATIONS-K5.md Addenda 4–5: B1, B2 and F1 are made and kept here).
  `Mag_bld`: a step that stays in BUILD keeps `Mag` when its explicit store gives B1/B2 for the new phase and F1 for every
  `first[]` cell. One theorem per phase, facts as `SafeBuild.lean` reads them.
-/
import K5.MagStep

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

theorem Mag_bld {b : Array Nat} {om : Nat} {σ σ' : Store} {p : Int} {f' : Int → Int} {H' : Finmap (fun _ : Int => Int)}
    (hS : stepS p σ = some σ') (hSe : stepS p σ = some ⟨H', σ.R⟩) (hw' : World σ' p (L0 b.size om) f')
    (hM : H'.lookup (p + cMODE) = some mBUILD)
    (hB1 : ∀ ph j c, H'.lookup (p + cPHASE) = some ph → H'.lookup (p + cINDEX) = some j →
      H'.lookup (p + cCODE) = some c → ph = 2 → 0 ≤ c ∧ c + 636 ≤ 636 * 2 ^ j.toNat)
    (hB2 : ∀ ph j le r t, H'.lookup (p + cPHASE) = some ph → H'.lookup (p + cINDEX) = some j →
      H'.lookup (p + cLEFT) = some le → H'.lookup (p + cREST) = some r → H'.lookup (p + cTOTAL) = some t → ph = 3 →
      0 ≤ le ∧ le ≤ 2 ^ j.toNat ∧ 0 ≤ r ∧ r ≤ 318 * j ∧ 0 ≤ t ∧ t ≤ 318 * j)
    (hF : ∀ t l : Int, 0 ≤ t → t ≤ 2 → 1 ≤ l → l ≤ 15 → ∀ v,
      H'.lookup (p + (tbase b.size om t + 16 + l)) = some v → 0 ≤ v ∧ v ≤ 636 * 2 ^ 16) :
    Mag b.size om f' := by
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have cell : ∀ c : Int, 0 ≤ c → c < b.size + om + 3626 → H'.lookup (p + c) = some (f' c) :=
    fun c a h => cell_after hS hSe hw' c a (by rw [hL0]; exact h)
  have eM := cell cMODE (by decide) (by unfold cMODE; omega)
  rw [hM] at eM
  have fM : f' cMODE = mBUILD := (Option.some.inj eM).symm
  have hem : em f' = mBUILD := by rw [em, if_neg (by rw [fM]; decide), fM]
  refine ⟨fun h => absurd (hem ▸ h) (by decide), fun h => absurd (hem ▸ h) (by decide), ?_,
    fun h => absurd (hem ▸ h) (by decide), fun h => absurd (hem ▸ h) (by decide), fun h => absurd (fM ▸ h) (by decide),
    fun _ h => hB1 _ _ _ (cell _ (by decide) (by unfold cPHASE; omega)) (cell _ (by decide) (by unfold cINDEX; omega))
      (cell _ (by decide) (by unfold cCODE; omega)) h,
    fun _ h => hB2 _ _ _ _ _ (cell _ (by decide) (by unfold cPHASE; omega)) (cell _ (by decide) (by unfold cINDEX; omega))
      (cell _ (by decide) (by unfold cLEFT; omega)) (cell _ (by decide) (by unfold cREST; omega))
      (cell _ (by decide) (by unfold cTOTAL; omega)) h, ?_⟩
  · intro h; rcases h with h | h | ⟨h, _⟩
    · exact absurd (hem ▸ h) (by decide)
    · exact absurd (hem ▸ h) (by decide)
    · exact absurd (fM ▸ h) (by decide)
  · intro t l a1 a2 a3 a4
    exact hF t l a1 a2 a3 a4 _ (cell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega))

theorem Mag_step_build0 {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD)
    (hph : f cPHASE = 0) (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hcell : ∀ c : Int, 0 ≤ c → c < b.size + om + 3626 → σ.H.lookup (p + c) = some (f c) :=
    fun c a h => hw.cell c a (by rw [hL0]; exact h)
  have hb := hi.2.cur
  rw [hm, facts_build] at hb
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨htg0, htg2, htbb, htgc, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  rw [htbb] at t0 tL
  have hmem : (mBUILD, buildN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mBUILD, buildN) hmem (by decide)
  have hj := hp0 hph
  by_cases h16 : f cINDEX < 16
  · have hSe := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (build_zero_cell hw (by unfold L0; omega) _ _ _ hph rfl hx htbb (by unfold X0; omega) (by rw [hL0]; unfold X0; omega)
        (by omega) h16 (by omega) (by rw [hL0]; unfold X0 at tL; omega))
    exact Mag_bld hS hSe hw' (by simp (disch := omega) only [cMODE, Finmap.lookup_insert_of_ne]; rw [hcell _ (by decide) (by omega)]; exact congrArg some hm) (by intro ph _ _ e _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro ph _ _ _ _ e _ _ _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro t l a1 a2 a3 a4 v e; simp (disch := (simp only [tbase, LB0, X0, cINDEX, cPHASE] at *; omega)) only [Finmap.lookup_insert_of_ne] at e; rw [hcell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)] at e; cases e; exact hg.f1 t l a1 a2 a3 a4)
  · have hSe := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (build_zero_end hw (by unfold L0; omega) _ _ _ hph rfl hx htbb (by unfold X0; omega) (by rw [hL0]; unfold X0; omega) h16)
    exact Mag_bld hS hSe hw' (by simp (disch := omega) only [cMODE, Finmap.lookup_insert_of_ne]; rw [hcell _ (by decide) (by omega)]; exact congrArg some hm) (by intro ph _ _ e _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro ph _ _ _ _ e _ _ _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro t l a1 a2 a3 a4 v e; simp (disch := (simp only [tbase, LB0, X0, cINDEX, cPHASE] at *; omega)) only [Finmap.lookup_insert_of_ne] at e; rw [hcell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)] at e; cases e; exact hg.f1 t l a1 a2 a3 a4)

theorem Mag_step_build1 {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD)
    (hph : f cPHASE = 1) (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hcell : ∀ c : Int, 0 ≤ c → c < b.size + om + 3626 → σ.H.lookup (p + c) = some (f c) :=
    fun c a h => hw.cell c a (by rw [hL0]; exact h)
  have hb := hi.2.cur
  rw [hm, facts_build] at hb
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨htg0, htg2, htbb, htgc, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  rw [htbb] at t0 tL
  have hmem : (mBUILD, buildN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mBUILD, buildN) hmem (by decide)
  obtain ⟨hj0, hjn, hz, hcn⟩ := hp1 hph
  by_cases hlt : f cINDEX < f (X0 b.size om + 6)
  · have hl := src_len hi s0 sL hj0 hlt
    have hSe := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (build_count_cell hw (by unfold L0; omega) _ _ _ _ _ _ _ hph rfl hx htbb rfl rfl (by unfold X0; omega)
        (by rw [hL0]; unfold X0; omega) hlt (by omega) (by rw [hL0]; omega) rfl (by omega) (by rw [hL0]; unfold X0 at tL; omega) hl.1 hl.2 rfl)
    split_ifs at hSe
    · exact Mag_bld hS hSe hw' (by simp (disch := omega) only [cMODE, Finmap.lookup_insert_of_ne]; rw [hcell _ (by decide) (by omega)]; exact congrArg some hm) (by intro ph _ _ e _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro ph _ _ _ _ e _ _ _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro t l a1 a2 a3 a4 v e; simp (disch := (simp only [tbase, LB0, X0, cINDEX, cPHASE] at *; omega)) only [Finmap.lookup_insert_of_ne] at e; rw [hcell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)] at e; cases e; exact hg.f1 t l a1 a2 a3 a4)
    · exact Mag_bld hS hSe hw' (by simp (disch := omega) only [cMODE, Finmap.lookup_insert_of_ne]; rw [hcell _ (by decide) (by omega)]; exact congrArg some hm) (by intro ph _ _ e _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro ph _ _ _ _ e _ _ _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro t l a1 a2 a3 a4 v e; simp (disch := (simp only [tbase, LB0, X0, cINDEX, cPHASE] at *; omega)) only [Finmap.lookup_insert_of_ne] at e; rw [hcell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)] at e; cases e; exact hg.f1 t l a1 a2 a3 a4)
  · have hSe := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (build_count_end hw (by unfold L0; omega) _ _ _ _ _ hph rfl hx htbb rfl rfl (by unfold X0; omega)
        (by rw [hL0]; unfold X0; omega) hlt (by omega) (by rw [hL0]; unfold X0 at tL; omega))
    refine Mag_bld hS hSe hw' (by simp (disch := omega) only [cMODE, Finmap.lookup_insert_of_ne]; rw [hcell _ (by decide) (by omega)]; exact congrArg some hm) ?_ (by intro ph _ _ _ _ e _ _ _ _ h; simp (disch := omega) only [cPHASE, Finmap.lookup_insert_of_ne] at e; first | (rw [Finmap.lookup_insert] at e; cases e; exact absurd h (by decide)) | (rw [hcell _ (by decide) (by omega)] at e; cases e; unfold cPHASE at hph; omega)) (by intro t l a1 a2 a3 a4 v e; simp (disch := (simp only [tbase, LB0, X0, cINDEX, cPHASE] at *; omega)) only [Finmap.lookup_insert_of_ne] at e; rw [hcell _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)] at e; cases e; exact hg.f1 t l a1 a2 a3 a4)
    -- entering phase 2: code := 0, j := 1, so B1 is 0 + 636 ≤ 1272
    intro ph j c eP eJ eC h
    simp (disch := omega) only [cPHASE, cINDEX, cCODE, Finmap.lookup_insert_of_ne] at eP eJ eC
    rw [Finmap.lookup_insert] at eJ eC
    cases eJ; cases eC; norm_num

end K5
