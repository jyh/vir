/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ at FIXLENS. The ⟶₅ step fills
  c = min(b − i, 32) cells of S5's fixed lengths in one fillR call, stopping at the run's end b = fixBndV i, so every cell
  of the chunk has the one length fixLenV i. DEFLATE writes one per step (fixlens_step); within a run fixLenI is constant
  (`fixLenV_run`), so c DEFLATE steps reach the same contents (`fixlens_iter`). At FILL = 318 both take DEFLATE's own end
  branch (the BUILD request, MODE := BUILD), j = 1.
-/
import VIRL5.FixlensRun5
import VIRL5.RefineRep5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- Within a run the fixed length is the run's. -/
theorem fixLenV_run (i k : Int) (h0 : 0 ≤ k) (hk : i + k < fixBndV i) : fixLenV (i + k) = fixLenV i := by
  unfold fixLenV fixBndV chain5 at *
  split_ifs at * <;> omega

/-- DEFLATE's contents after c FIXLENS steps that all write the length v, relative to the base. -/
def fixRel (g : Int → Int) (fl : Int) (n om : Nat) (v : Int) (c : Nat) : Int → Int :=
  Function.update (fun j => if 2080 + n + om + fl ≤ j ∧ j < 2080 + n + om + fl + c then v else g j) cFILL (fl + c)

theorem fixlens_mem : (mFIXLENS, fixlensN) ∈ modes := by simp [modes]

theorem fixlens_iter {p : Int} {L : Nat} (n om : Nat) (hL : 2080 + n + om + 318 ≤ L) (v : Int) :
    ∀ (c : Nat) (σ : Store) (g : Int → Int) (fl : Nat),
    World σ p L g → g cMODE = mFIXLENS → g cFILL = fl → g cN = n → g cOUTMAX = om → fl + c ≤ 318 →
    (∀ k : Nat, k < c → fixLenI ((fl : Int) + k) = v) →
    ∃ σ', iterS p c σ = some σ' ∧ World σ' p L (fixRel g fl n om v c)
  | 0, σ, g, fl, hw, _, hfl, _, _, _, _ =>
    ⟨σ, rfl, world_congr hw (fun i _ _ => by
      unfold fixRel
      simp only [Function.update_apply, Nat.cast_zero, add_zero]
      split_ifs with h1 h2 <;> (try subst_vars) <;> first | omega | simp_all)⟩
  | c + 1, σ, g, fl, hw, hm, hfl, hn, hom, hc, hv => by
    have hfit := modes_fit (mFIXLENS, fixlensN) fixlens_mem (by decide)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (fixlens_step hw fl n om hL hfl (by omega) hn hom)
    have hv0 : fixLenI (fl : Int) = v := by simpa using hv 0 (by omega)
    have hw1 := (hw.store (i := 2080 + n + om + fl) (v := fixLenI fl) (by omega) (by omega)).store
      (i := 10) (v := (fl : Int) + 1) (by omega) (by omega)
    set g1 := Function.update (Function.update g (2080 + n + om + fl) (fixLenI fl)) 10 ((fl : Int) + 1) with hg1
    have u : ∀ d : Int, d ≠ 2080 + n + om + fl → d ≠ 10 → g1 d = g d := by
      intro d h1 h2; simp [hg1, Function.update_apply, h1, h2]
    obtain ⟨σ', hit, hw'⟩ := fixlens_iter n om hL v c _ g1 (fl + 1) hw1
      (by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm)
      (by show g1 10 = ((fl + 1 : Nat) : Int); simp [hg1, Function.update_apply])
      (by rw [u _ (by unfold cN; omega) (by unfold cN; omega)]; exact hn)
      (by rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)]; exact hom)
      (by omega)
      (fun k hk => by
        have := hv (k + 1) (by omega)
        rw [show ((fl + 1 : Nat) : Int) + (k : Int) = (fl : Int) + ((k + 1 : Nat) : Int) by push_cast; ring]
        exact this)
    refine ⟨σ', by simp only [iterS, hS, Option.bind_some]; exact hit, world_congr hw' (fun i _ _ => ?_)⟩
    simp only [fixRel, hg1, Function.update_apply, cFILL]
    push_cast
    split_ifs <;> first | omega | rfl | exact hv0 | exact hv0.symm

theorem refine_fixlens (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f) (hm : f cMODE = mFIXLENS) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hLv : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hwf := wf_of_sole hw hs (by omega)
  have hc := hi.2.cur
  rw [hm, facts_fixlens] at hc
  obtain ⟨hf0, hf318⟩ := hc
  have hn := hi.1.n_eq
  have hom := hi.1.om_eq
  have hlk : modes₅.lookup (f cMODE) = some (fixlensT₅.shift 0) := by rw [hm]; rfl
  have hfit := modes_fit (mFIXLENS, fixlensN) fixlens_mem (by decide)
  obtain ⟨i, hi'⟩ : ∃ i : Nat, f cFILL = i := ⟨(f cFILL).toNat, by omega⟩
  by_cases hlt : (i : Int) < 318
  · -- one chunk, up to the run's end
    have hb := fixBndV_gt i hlt
    have hb2 := fixBndV_le i
    obtain ⟨c, hcd⟩ : ∃ c : Int, c = min (fixBndV i - i) CS := ⟨_, rfl⟩
    have hc32 : c ≤ 32 := by rw [hcd]; unfold CS; omega
    have hc0 : 0 < c := by rw [hcd]; unfold CS; omega
    have hcb : (i : Int) + c ≤ fixBndV i := by rw [hcd]; omega
    have hcT : (c.toNat : Int) = c := Int.toNat_of_nonneg (by omega)
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 3 * 32 + 20) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (fixlensPostRel p f i b.size om) ∧ Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := fixlens5_chunk_world p (L0 b.size om) f i b.size om hi' (by omega) hlt hn hom
          (by omega) (by omega) (by unfold IN; omega) hw hs hwf (F := F) (by rw [← hcd]; omega)
        exact ⟨a, h1, h2, h3, h4⟩)
    obtain ⟨σD, hit, hwD⟩ := fixlens_iter b.size om (by unfold L0; omega) (fixLenV i) c.toNat σ f i hw hm hi' hn hom
      (by omega) (fun k hk => by
        rw [fixLenI_eq_V]
        exact fixLenV_run i k (by omega) (by omega))
    have hsD := iterS_sole _ σ σD hs hit
    have e := sole_world_eq' hwL hsL hwD hsD (fun j h0 h1 => by
      simp only [fixRel, fixlensPostRel, fixlensPost]
      simp only [← hcd, hcT, Function.update_apply, fillF, add_right_inj, add_sub_cancel_left, cFILL, IN]
      split_ifs <;> first | omega | (congr 1; omega) | simp_all)
    subst e
    exact ⟨c.toNat, _, hstL, hit, hsL, fun _ _ => by omega⟩
  · -- the end: DEFLATE's own branch, j = 1
    have h318 : f cFILL = 318 := by omega
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 18) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (fixlensEndPostRel p f b.size om (f cLIT) (X0 b.size om)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := fixlens5_end_world p (L0 b.size om) f i b.size om (f cLIT) (X0 b.size om) hi' hlt
          hn hom rfl hi.1.x_eq (by omega) (by omega) hL0 hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (fixlens_end hw hL0 b.size om (f cLIT) (X0 b.size om) h318 hn hom rfl hi.1.x_eq (by omega) (by omega))
    have hwD := ((((((((((((hw.store (i := X0 b.size om + 5) (v := 2080 + b.size + om) (by omega) (by omega)).store
      (i := X0 b.size om + 6) (v := 288) (by omega) (by omega)).store
      (i := X0 b.size om + 7) (v := 2080 + b.size + om + 689) (by omega) (by omega)).store
      (i := X0 b.size om + 8) (v := 0) (by omega) (by omega)).store (i := 7) (v := 288) (by omega) (by omega)).store
      (i := 8) (v := 30) (by omega) (by omega)).store (i := 2072) (v := f cLIT) (by omega) (by omega)).store
      (i := 12) (v := 0) (by omega) (by omega)).store (i := 13) (v := 0) (by omega) (by omega)).store
      (i := 2074) (v := 1) (by omega) (by omega)).store (i := 2073) (v := 0) (by omega) (by omega)).store
      (i := 0) (v := 11) (by omega) (by omega))
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun j h0 h1 => by
      simp only [fixlensEndPostRel, fixlensEndPost, Function.update_apply, add_right_inj, add_sub_cancel_left, cHLIT,
        cHDIST, cCHK, cPHASE, cINDEX, cTGT, cDYN, cMODE, mBUILD, IN])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩

end VIRL5
