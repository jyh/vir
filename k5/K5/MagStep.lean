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

/-- **Every clause vacuous:** the new mode is neither DECODE nor BUILD, the mode returned to is none of the PEND/DIST modes,
and the `first[]` cells are those of a world satisfying `Mag` (F1 is the only clause that is not mode-conditioned). -/
theorem Mag_vac {n om : Nat} {f g : Int → Int} (hg : Mag n om f) (hD : g cMODE ≠ mDECODE) (hB : g cMODE ≠ mBUILD)
    (he1 : em g ≠ mSNLEN) (he2 : em g ≠ mLENX) (he3 : em g ≠ mDSTD) (he4 : em g ≠ mDSTX) (he5 : em g ≠ mLREP)
    (hF : ∀ t l : Int, 0 ≤ t → t ≤ 2 → 1 ≤ l → l ≤ 15 → g (tbase n om t + 16 + l) = f (tbase n om t + 16 + l)) :
    Mag n om g := by
  refine ⟨fun h => absurd h he1, fun h => absurd h he2, ?_, fun h => absurd h he5, fun h => absurd h he4,
    fun h => absurd h hD, fun h => absurd h hB, fun h => absurd h hB, ?_⟩
  · intro h; rcases h with h | h | ⟨h, _⟩
    · exact absurd h he3
    · exact absurd h he4
    · exact absurd h hD
  · intro t l a1 a2 a3 a4; rw [hF t l a1 a2 a3 a4]; exact hg.f1 t l a1 a2 a3 a4

/-- A READ request (`reqF`) returning to a mode that carries no clause keeps `Mag`, given the cells it changed first. -/
theorem Mag_reqF_vac {n om : Nat} {f f₁ : Int → Int} (hg : Mag n om f) {k rt : Int}
    (hrt : rt ≠ mSNLEN ∧ rt ≠ mLENX ∧ rt ≠ mDSTD ∧ rt ≠ mDSTX ∧ rt ≠ mLREP)
    (hF : ∀ t l : Int, 0 ≤ t → t ≤ 2 → 1 ≤ l → l ≤ 15 → f₁ (tbase n om t + 16 + l) = f (tbase n om t + 16 + l)) :
    Mag n om (reqF f₁ k rt) := by
  have gM : reqF f₁ k rt cMODE = mREAD := by simp [reqF, cMODE, mREAD]
  have gR : reqF f₁ k rt cRET = rt := by simp [reqF, cRET]
  have gem : em (reqF f₁ k rt) = rt := by rw [em, if_pos gM, gR]
  refine Mag_vac hg (by rw [gM]; decide) (by rw [gM]; decide) (by rw [gem]; exact hrt.1) (by rw [gem]; exact hrt.2.1)
    (by rw [gem]; exact hrt.2.2.1) (by rw [gem]; exact hrt.2.2.2.1) (by rw [gem]; exact hrt.2.2.2.2) ?_
  intro t l a1 a2 a3 a4
  have : 2080 ≤ tbase n om t + 16 + l := by unfold tbase LB0; omega
  simp only [reqF, Function.update_apply]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hF t l a1 a2 a3 a4

theorem Mag_step_hdr {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mHDR)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  obtain ⟨hSe, hwe, -, -⟩ := safe_hdr' (b := b) (om := om) (lit := lit) hw (by unfold L0; omega) hi.1 hm
  exact Mag_of_explicit hS hSe hw' hwe (Mag_reqF_vac hg (by decide) (fun _ _ _ _ _ _ => rfl))

theorem Mag_step_hdrb {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mHDRB)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  obtain ⟨hSe, hwe, -, -⟩ := safe_hdrb (b := b) (om := om) (lit := lit) hw (by unfold L0; omega) hi.1 hm
  refine Mag_of_explicit hS hSe hw' hwe (Mag_reqF_vac hg (by decide) ?_)
  intro t l a1 a2 a3 a4
  rw [Function.update_apply, if_neg (by unfold tbase LB0; omega)]

theorem Mag_step_dhdr {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mDHDR)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  obtain ⟨hSe, hwe, -, -⟩ := safe_dhdr (b := b) (om := om) (lit := lit) hw (by unfold L0; omega) hi.1 hm
  exact Mag_of_explicit hS hSe hw' hwe (Mag_reqF_vac hg (by decide) (fun _ _ _ _ _ _ => rfl))

/-- After a step whose store is pinned to `⟨H', σ.R⟩`, each region cell of the new world is read off `H'`. -/
theorem cell_after {σ σ' : Store} {p : Int} {L : Nat} {f' : Int → Int} {H' : Finmap (fun _ : Int => Int)}
    (hS : stepS p σ = some σ') (hSe : stepS p σ = some ⟨H', σ.R⟩) (hw' : World σ' p L f') (c : Int) (h0 : 0 ≤ c)
    (h1 : c < L) : H'.lookup (p + c) = some (f' c) := by
  rw [hS] at hSe; cases hSe; exact hw'.cell c h0 h1

/-- A cell the step did not write keeps its value. -/
theorem cell_frame {σ : Store} {p : Int} {L : Nat} {f f' : Int → Int} (hw : World σ p L f) {c : Int} (h0 : 0 ≤ c)
    (h1 : c < L) (h : σ.H.lookup (p + c) = some (f' c)) : f' c = f c := by
  rw [hw.cell c h0 h1] at h; exact (Option.some.inj h).symm

/-- `Mag_vac` read off a pinned store: the new mode `m` (not READ, DECODE or BUILD, nor a PEND/DIST mode) and the step
writing none of the `first[]` cells. -/
theorem Mag_pinned {b : Array Nat} {om : Nat} {σ σ' : Store} {p : Int} {f f' : Int → Int} {H' : Finmap (fun _ : Int => Int)}
    (hw : World σ p (L0 b.size om) f) (hg : Mag b.size om f) (hS : stepS p σ = some σ') (hSe : stepS p σ = some ⟨H', σ.R⟩)
    (hw' : World σ' p (L0 b.size om) f')
    (hm : ∀ m, H'.lookup (p + cMODE) = some m →
      m ≠ mREAD ∧ m ≠ mDECODE ∧ m ≠ mBUILD ∧ m ≠ mSNLEN ∧ m ≠ mLENX ∧ m ≠ mDSTD ∧ m ≠ mDSTX ∧ m ≠ mLREP)
    (hF : ∀ t l : Int, 0 ≤ t → t ≤ 2 → 1 ≤ l → l ≤ 15 →
      H'.lookup (p + (tbase b.size om t + 16 + l)) = σ.H.lookup (p + (tbase b.size om t + 16 + l))) :
    Mag b.size om f' := by
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have eM := cell_after hS hSe hw' cMODE (by decide) (by rw [hL0]; unfold cMODE; omega)
  have hm' := hm _ eM
  have hem : em f' = f' cMODE := by rw [em, if_neg hm'.1]
  refine Mag_vac hg hm'.2.1 hm'.2.2.1 (by rw [hem]; exact hm'.2.2.2.1)
    (by rw [hem]; exact hm'.2.2.2.2.1) (by rw [hem]; exact hm'.2.2.2.2.2.1) (by rw [hem]; exact hm'.2.2.2.2.2.2.1)
    (by rw [hem]; exact hm'.2.2.2.2.2.2.2) ?_
  intro t l a1 a2 a3 a4
  have h0 : 0 ≤ tbase b.size om t + 16 + l := by unfold tbase LB0; omega
  have h1 : tbase b.size om t + 16 + l < (L0 b.size om : Int) := by rw [hL0]; unfold tbase LB0; omega
  have e := cell_after hS hSe hw' _ h0 h1
  rw [hF t l a1 a2 a3 a4] at e
  exact cell_frame hw h0 h1 e

theorem Mag_step_hdrd {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hg : Mag b.size om f) (hm : f cMODE = mHDRD)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mHDRD, hdrdN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mHDRD, hdrdN) hmem (by decide)
  have hSe := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (hdrd_step hw hL (f cACC) rfl)
  have ne : ∀ (c d : Int), c ≠ d → p + c ≠ p + d := fun c d h e => h (by omega)
  unfold hdrdH at hSe
  split_ifs at hSe
  all_goals refine Mag_pinned hw hg hS hSe hw' (fun m e => ?_) ?_
  all_goals try (rw [show p + cMODE = p + 0 from rfl, Finmap.lookup_insert] at e; cases e; simp [mREAD, mDECODE, mBUILD, mSNLEN, mLENX, mDSTD, mDSTX, mLREP])
  all_goals intro t l a1 a2 a3 a4
  all_goals simp only [Finmap.lookup_insert_of_ne _ (ne _ _ (show tbase b.size om t + 16 + l ≠ 0 by unfold tbase LB0; omega)),
    Finmap.lookup_insert_of_ne _ (ne _ _ (show tbase b.size om t + 16 + l ≠ 10 by unfold tbase LB0; omega)),
    Finmap.lookup_insert_of_ne _ (ne _ _ (show tbase b.size om t + 16 + l ≠ 14 by unfold tbase LB0; omega))]

end K5
