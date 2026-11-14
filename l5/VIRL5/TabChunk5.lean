/-
  O95 layer L5, Lean arm (STATUS 323, fork (T)): `Tab` survives one DEFLATE step in the three chunked modes whose stores go to
  a computed cell (the output, or the code-length area): COPY, SCOPY and REP. Each step is the c = 1 instance of the mode's own
  iterate (`copy_iter`, `scopy_iter`, `rep_iter`) or its end branch, and every cell either writes is a control cell or lies at
  2080 or above, outside the table [20, 2068). The bounds are Safety's, read as the Refine₅ cases read them.
-/
import VIRL5.TabKeep5
import VIRL5.RefineCopy5
import VIRL5.RefineScopy5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- Tab carries to any world of a store whose explicit contents g keep the table, from a non-TABLE mode. -/
theorem tab_of_world {σ' : Store} {p : Int} {L : Nat} {f g f' : Int → Int} (hL : 2068 ≤ L)
    (hg : World σ' p L g) (hw' : World σ' p L f') (ha : ∀ c : Int, 20 ≤ c → c < 2068 → g c = f c)
    (hnt : f cMODE ≠ mTABLE) (h : Tab f) : Tab f' := by
  unfold Tab at h
  rw [if_neg hnt] at h
  unfold Tab
  apply bits_all
  intro v i hv hi hlt
  rw [hw'.agree hg (i := BT + (8 * v + i)) (by unfold BT; omega) (by unfold BT; omega),
    ha _ (by unfold BT; omega) (by unfold BT; omega)]
  exact h v i hv hi hlt

/-- One step of the iterate is the step. -/
theorem stepS_of_iter1 {p : Int} {σ σ' : Store} (h : iterS p 1 σ = some σ') : stepS p σ = some σ' := by
  simpa [iterS] using h

/-- The forward copy writes only at and above its destination. -/
theorem cwR_below : ∀ (c : Nat) (g : Int → Int) (s d i : Int), i < d → cwR g s d c i = g i
  | 0, _, _, _, _, _ => rfl
  | c + 1, g, s, d, i, h => by
    simp only [cwR]
    rw [cwR_below c _ (s + 1) (d + 1) i (by omega), Function.update_apply, if_neg (by omega)]

theorem tab_copy {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mCOPY) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hLv : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hom := hi.1.om_eq
  have hmr := hi.1.m_rng
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hfit := modes_fit (mCOPY, copyN) copy_mem (by decide)
  by_cases hpd : f cPEND = 0
  · have hS' := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (copy_end hw hL0 hpd)
    rw [hS'] at hS
    cases hS
    exact tab_of_world (by omega) (hw.store (i := 0) (v := 13) (by omega) (by omega)) hw'
      (fun c h0 _ => by rw [Function.update_apply, if_neg (by omega)]) hnt hT
  · have hc := hi.2.cur
    rw [hm, facts_copy] at hc
    obtain ⟨-, -, hp0, hd0, hdm, hmo⟩ := hc
    have hn := hi.1.n_eq
    obtain ⟨σD, hit, hwD⟩ := copy_iter hL0 b.size (f cDIST) 1 σ f (f cPEND) (f cM) hw hm rfl hn rfl rfl
      (by push_cast; omega) hd0 hdm (by omega) (by push_cast; omega)
    rw [stepS_of_iter1 hit] at hS
    cases hS
    exact tab_of_world (by omega) hwD hw' (fun c h0 h1 => by
      simp only [copyRel, Function.update_apply]
      rw [if_neg (by unfold cPEND; omega), if_neg (by unfold cM; omega), cwR_below 1 f _ _ c (by omega)]) hnt hT

theorem tab_scopy {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSCOPY) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hLv : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hom := hi.1.om_eq
  have hmr := hi.1.m_rng
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hfit := modes_fit (mSCOPY, scopyN) scopy_mem (by decide)
  by_cases hpd : f cPEND = 0
  · have hS' := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (scopy_end hw hL0 (f cBF) hpd rfl)
    rw [hS'] at hS
    cases hS
    exact tab_of_world (by omega) (hw.store (i := 0) (v := if f cBF = 1 then 98 else 1) (by omega) (by omega)) hw'
      (fun c h0 _ => by rw [Function.update_apply, if_neg (by omega)]) hnt hT
  · have hc := hi.2.cur
    rw [hm] at hc
    simp only [facts, show mSCOPY = (10 : Int) by rfl, show ¬ ((10 : Int) = mSNLEN) by decide, if_false, if_true] at hc
    obtain ⟨hp0, hmo⟩ := hc
    have hsc := hi.2.scopy hm
    have hn := hi.1.n_eq
    have hbr := hi.1.by_rng
    have hmr := hi.1.m_rng
    have hbxT : ((f cBY).toNat : Int) = f cBY := Int.toNat_of_nonneg hbr.1
    have hmT : ((f cM).toNat : Int) = f cM := Int.toNat_of_nonneg hmr.1
    obtain ⟨σD, hit, hwD⟩ := scopy_iter b.size om (by unfold L0; omega) 1 σ f (f cPEND) (f cBY).toNat (f cM).toNat
      hw hm rfl (by rw [hbxT]) hn (by rw [hmT]) (by push_cast; omega) (by omega) (by omega)
    rw [stepS_of_iter1 hit] at hS
    cases hS
    exact tab_of_world (by omega) hwD hw' (fun c h0 h1 => by
      simp only [scopyRel, Function.update_apply, cM, cPEND, cBY]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), cwR_below 1 f _ _ c (by omega)]) hnt hT

theorem tab_rep {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mREP) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hLv : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hom := hi.1.om_eq
  have hmr := hi.1.m_rng
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hfit := modes_fit (mREP, repN) rep_mem (by decide)
  by_cases hpd : f cPEND = 0
  · have hS' := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (rep_end hw hL0 hpd)
    rw [hS'] at hS
    cases hS
    exact tab_of_world (by omega) (hw.store (i := 0) (v := 12) (by omega) (by omega)) hw'
      (fun c h0 _ => by rw [Function.update_apply, if_neg (by omega)]) hnt hT
  · have hc := hi.2.cur
    rw [hm, facts_rep] at hc
    obtain ⟨hf0, hp0, hfp, hhl, hhd, -, -, -⟩ := hc
    have hn := hi.1.n_eq
    have hom := hi.1.om_eq
    obtain ⟨σD, hit, hwD⟩ := rep_iter hL0 (f cLAST) b.size om 1 σ f (f cPEND) (f cFILL) hw hm rfl rfl rfl hn hom
      (by push_cast; omega) (by omega) (by push_cast; omega)
    rw [stepS_of_iter1 hit] at hS
    cases hS
    exact tab_of_world (by omega) hwD hw' (fun c h0 h1 => by
      simp only [repRel, Function.update_apply]
      rw [if_neg (by unfold cPEND; omega), if_neg (by unfold cFILL; omega), if_neg (by omega)]) hnt hT

end VIRL5
