/-
  O95 layer L5, Lean arm (STATUS 323, LV8-MAP Addendum 6, fork (T)): Refine₅ at READ. The ⟶₅ step reads the bit through bitR,
  arithmetically (`bitsF`, the byte's bit); DEFLATE's step reads the table cell 8·v + bi. Under (T), outside TABLE the table is
  S1's (`BitsUpTo f 2048`), so the two bits are equal and the two stores are the same (j = 1). By ≥ n: both take DEFLATE's own
  TRUNC branch.
-/
import VIRL5.TabStep5
import VIRL5.ReadRun5
import VIRL5.DecodeRun5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The cursor's carry, as tblNext and as bitR's next position. -/
theorem tblNext_pos (bx bi : Int) (h0 : 0 ≤ bi) (h7 : bi ≤ 7) :
    (tblNext bx bi).1 = ((8 * (IN + bx) + bi) + 1) / 8 - IN ∧ (tblNext bx bi).2 = ((8 * (IN + bx) + bi) + 1) % 8 := by
  unfold tblNext IN
  split_ifs <;> simp <;> omega

/-- bitR's one bit is the byte's bit. -/
theorem bitsF_one (f : Int → Int) (p bx bi : Int) (h0 : 0 ≤ bi) (h7 : bi ≤ 7) :
    bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 = VIRDeflate.bitAt (f (IN + bx)) bi.toNat := by
  have hd : (8 * (IN + bx) + bi) / 8 = IN + bx := by unfold IN; omega
  have hm : (8 * (IN + bx) + bi) % 8 = bi := by unfold IN; omega
  simp only [bitsF, hd, hm, show p + (IN + bx) - p = IN + bx by ring, mul_zero, add_zero]

theorem refine_read (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f)
    (hT : Tab f) (hm : f cMODE = mREAD) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hwf := wf_of_sole hw hs (by unfold L0; omega)
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hlk : modes₅.lookup (f cMODE) = some (readT₅.shift 0) := by rw [hm]; rfl
  have hmem : (mREAD, readN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mREAD, readN) hmem (by decide)
  have hbits : BitsUpTo f 2048 := by unfold Tab at hT; rwa [if_neg hnt] at hT
  by_cases hlt : f cBY < b.size
  · obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set v := b[(f cBY).toNat]'(by omega) with hvdef
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have hbyE : ((f cBY).toNat : Int) = f cBY := by omega
    rw [hbyE] at hv
    have htab : f (BT + (8 * (v : Int) + f cBI)) = VIRDeflate.bitAt v (f cBI).toNat := by
      have := hbits v (f cBI).toNat hv8 (by omega) (by omega)
      rwa [hbiE] at this
    have hbit : bitsF (fun a => f (a - p)) p (8 * (IN + f cBY) + f cBI) 1 = f (BT + (8 * (v : Int) + f cBI)) := by
      rw [bitsF_one f p _ _ hir.1 hir.2, hv, htab]
    obtain ⟨htn1, htn2⟩ := tblNext_pos (f cBY) (f cBI) hir.1 hir.2
    have hstep := readbit_step hw (f cBY).toNat (f cBI).toNat b.size v (f cK) (f cACC) (f cWT) (f cRET)
      (f (BT + (8 * (v : Int) + f cBI))) hL0 (by omega) (by omega) hn (by omega) (by omega) (by rw [hbyE]; exact hv) hv8
      (by rw [hbiE]) rfl rfl rfl rfl
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2 hstep
    simp only [hbyE, hbiE] at hS
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by unfold L0; omega) hlk (F₀ := 276) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (readPostRel p f (f cBY) (f cBI) (f cK) (f cACC) (f cWT) (f cRET)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := read5_bit_world p (L0 b.size om) f (f cBY) (f cBI) b.size (f cK) (f cACC) (f cWT)
          (f cRET) rfl rfl hn rfl rfl rfl rfl hbr.1 hlt hir.1 hir.2 (by unfold IN; omega) hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    set t := f (BT + (8 * (v : Int) + f cBI)) with htd
    set f1 := Function.update (Function.update (Function.update (Function.update (Function.update f cBY
      (tblNext (f cBY) (f cBI)).1) cBI (tblNext (f cBY) (f cBI)).2) cACC (f cACC + t * f cWT)) cWT (2 * f cWT)) cK
      (f cK - 1) with hf1
    have hw1 : World ⟨rdH σ.H p (f cBY) (f cBI) (f cACC) (f cWT) (f cK) t, σ.R⟩ p (L0 b.size om) f1 := by
      unfold rdH
      exact ((((hw.store (i := 1) (by norm_num) (by unfold L0; omega)).store (i := 2) (by norm_num) (by unfold L0; omega)).store
        (i := 2069) (by norm_num) (by unfold L0; omega)).store (i := 2070) (by norm_num) (by unfold L0; omega)).store
        (i := 2068) (by norm_num) (by unfold L0; omega)
    have key : ∀ i : Int, readPostRel p f (f cBY) (f cBI) (f cK) (f cACC) (f cWT) (f cRET) i =
        (if f cK - 1 = 0 then Function.update f1 cMODE (f cRET) else f1) i := by
      intro i
      simp only [readPostRel, readPost, hbit, hf1, ← htn1, ← htn2, ite_apply, Function.update_apply, add_right_inj,
        add_sub_cancel_left]
      all_goals (split_ifs <;> first | rfl | (simp only [cBY, cBI, cACC, cWT, cK, cMODE] at *; omega))
    by_cases hk : f cK - 1 = 0
    · rw [if_pos hk] at hS
      have hwD := hw1.store (i := 0) (v := f cRET) (by norm_num) (by unfold L0; omega)
      have hsD := stepS_sole hs hS
      have e := sole_world_eq' hwL hsL hwD hsD (fun i _ _ => by rw [key i, if_pos hk]; rfl)
      subst e
      exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
    · rw [if_neg hk] at hS
      have hsD := stepS_sole hs hS
      have e := sole_world_eq' hwL hsL hw1 hsD (fun i _ _ => by rw [key i, if_neg hk])
      subst e
      exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by unfold L0; omega) hlk (F₀ := 6) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om)
          (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cREASON) rTRUNC) (p + cMODE) mREJECT (p + i)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := read5_trunc_world p (L0 b.size om) f (f cBY) (f cBI) b.size rfl rfl hn hlt
          (by unfold L0; omega) hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (readbit_trunc hw (by unfold L0; omega) (f cBY) b.size rfl hn (by omega))
    have hwD := (hw.store (i := 14) (v := 1) (by norm_num) (by unfold L0; omega)).store (i := 0) (v := 99) (by norm_num)
      (by unfold L0; omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i _ _ => by
      simp only [Function.update_apply, add_right_inj, add_sub_cancel_left, cREASON, cMODE, rTRUNC, mREJECT])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩

theorem refine_decode (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f)
    (hT : Tab f) (hm : f cMODE = mDECODE) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hLn : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hwf := wf_of_sole hw hs (by omega)
  have hmem : (mDECODE, decodeN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDECODE, decodeN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hlk : modes₅.lookup (f cMODE) = some (decodeT₅.shift 0) := by rw [hm]; rfl
  have hbits : BitsUpTo f 2048 := by unfold Tab at hT; rwa [if_neg hnt] at hT
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  obtain ⟨hfr, hl1, hl15, hpair, hsane⟩ := hi.2.dec hm
  have ht02 : 0 ≤ f (X0 b.size om + 2) ∧ f (X0 b.size om + 2) ≤ 2 := by
    rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  by_cases hlt : f cBY < b.size
  · obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set v := b[(f cBY).toNat]'(by omega) with hvdef
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have hbyE : ((f cBY).toNat : Int) = f cBY := by omega
    have hv' : f (IN + f cBY) = v := by rw [← hbyE]; exact hv
    have htab : f (BT + (8 * (v : Int) + f cBI)) = VIRDeflate.bitAt v (f cBI).toNat := by
      have := hbits v (f cBI).toNat hv8 (by omega) (by omega)
      rwa [hbiE] at this
    set bit := f (BT + (8 * (v : Int) + f cBI)) with hbitd
    have hbit : bitsF (fun a => f (a - p)) p (8 * (IN + f cBY) + f cBI) 1 = bit := by
      rw [bitsF_one f p _ _ hir.1 hir.2, hv']; exact htab.symm
    obtain ⟨htn1, htn2⟩ := tblNext_pos (f cBY) (f cBI) hir.1 hir.2
    set l := f (X0 b.size om) with hld
    set t := f (X0 b.size om + 2) with htd
    set rt := f (X0 b.size om + 3) with hrtd
    set cv := f (X0 b.size om + 1) with hcvd
    set tb : Int := 2080 + (b.size : Int) + om + 337 + 352 * t with htbd
    have hs' := hsane l hl1 hl15
    have htb : tbase b.size om t = tb := by rw [htbd]; unfold tbase LB0; ring
    rw [htb] at hs'
    set fs := f (tb + 16 + l) with hfsd
    set c := f (tb + l) with hcd
    set o := f (tb + 32 + l) with hod
    set sy := f (tb + 64 + o + (2 * cv + bit - fs)) with hsyd
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_step hw (f cBY).toNat (f cBI).toNat b.size v om (X0 b.size om) l cv t rt
        (f (BT + (8 * (v : Int) + ((f cBI).toNat : Int)))) tb fs c o
        (f (tb + 64 + o + (2 * cv + f (BT + (8 * (v : Int) + ((f cBI).toNat : Int))) - fs))) hLn (by omega) (by omega) hn
        hi.1.om_eq hi.1.x_eq (by omega) (by omega) hv hv8 rfl (by omega) (by omega) rfl rfl rfl rfl htbd.symm (by omega)
        (by omega) hl1 hl15 rfl rfl rfl (fun hh => ⟨by omega, by omega⟩) rfl)
    simp only [hbyE, hbiE] at hS
    rw [← hbitd, ← hsyd] at hS
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 280) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om)
          (decPostRel p f (f cBY) (f cBI) (X0 b.size om) l rt fs c (2 * cv + bit) sy) ∧ Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := decode5_bit_world p (L0 b.size om) f (f cBY) (f cBI) b.size om (X0 b.size om) l cv t
          rt tb fs c o sy rfl rfl hn hi.1.om_eq hi.1.x_eq hbr.1 hlt hir.1 hir.2 (by unfold IN; omega) (by omega) (by omega)
          rfl rfl rfl rfl (by rw [htbd]; unfold IN; ring) (by omega) (by omega) hl1 hl15 rfl rfl
          (fun _ => rfl) (fun hh => by rw [hbit] at hh ⊢; exact ⟨by omega, by omega⟩) (fun _ => by rw [hbit])
          hw hs hwf hF
        rw [hbit] at h3
        exact ⟨a, h1, h2, h3, h4⟩)
    set X := X0 b.size om with hXd
    set gD : Int → Int := if fs ≤ 2 * cv + bit ∧ 2 * cv + bit < fs + c then
        Function.update (Function.update (Function.update (Function.update f cBY (tblNext (f cBY) (f cBI)).1) cBI
          (tblNext (f cBY) (f cBI)).2) (X + 4) sy) cMODE rt
      else if l = 15 then Function.update (Function.update f cREASON rINVCODE) cMODE mREJECT
      else Function.update (Function.update (Function.update (Function.update f cBY (tblNext (f cBY) (f cBI)).1) cBI
          (tblNext (f cBY) (f cBI)).2) X (l + 1)) (X + 1) (2 * cv + bit) with hgD
    have hwD : World ⟨decH σ.H p (f cBY) (f cBI) X l rt fs c (2 * cv + bit) sy, σ.R⟩ p (L0 b.size om) gD := by
      rw [hgD]
      unfold decH
      split_ifs
      · exact (((hw.store (i := 1) (by norm_num) (by omega)).store (i := 2) (by norm_num) (by omega)).store (i := X + 4)
          (by omega) (by omega)).store (i := 0) (by norm_num) (by omega)
      · exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
      · exact (((hw.store (i := 1) (by norm_num) (by omega)).store (i := 2) (by norm_num) (by omega)).store (i := X)
          (by omega) (by omega)).store (i := X + 1) (by omega) (by omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i _ _ => by
      rw [hgD]
      simp only [decPostRel, decPost, ← htn1, ← htn2, ite_apply, Function.update_apply, add_right_inj,
        add_sub_cancel_left]
      all_goals (split_ifs <;> first | rfl | (simp only [cBY, cBI, cMODE, cREASON] at *; omega)))
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 8) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om)
          (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cREASON) rTRUNC) (p + cMODE) mREJECT (p + i)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := decode5_trunc_world p (L0 b.size om) f (f cBY) (f cBI) b.size rfl rfl hn hlt hL
          hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_trunc hw hL (f cBY) (f cBI) b.size om (X0 b.size om) rfl rfl hn hi.1.om_eq hi.1.x_eq (by omega))
    have hwD := (hw.store (i := 14) (v := 1) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i _ _ => by
      simp only [Function.update_apply, add_right_inj, add_sub_cancel_left, cREASON, cMODE, rTRUNC, mREJECT])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩

end VIRL5
