/-
  O95 layer L5, Lean arm (STATUS 323, fork (T)): `Tab` survives one DEFLATE step in SYM, LENX, CLPUT, SYMD and LSYM, the modes
  whose stores go to the X area (a decode request), the output (a literal) or the code-length area. Each step is DEFLATE's own
  step lemma with Safety's premises, read as Safety reads them; its store is an explicit chain of inserts, and every insert
  is a control cell or lies at 2080 or above, so the table cells are as they were (`TKeep`) and `tab_of_tkeep` carries Tab.
-/
import VIRL5.TabChunk5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A step to an explicit store that keeps the table carries Tab. -/
theorem tab_of_stepH {b : Array Nat} {om : Nat} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    {H : Finmap (fun _ : Int => Int)} (hw : World σ p (L0 b.size om) f) (hS0 : stepS p σ = some ⟨H, σ.R⟩)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f')
    (hk : ∀ c : Int, 20 ≤ c → c < 2068 → H.lookup (p + c) = σ.H.lookup (p + c)) (hnt : f cMODE ≠ mTABLE) (hT : Tab f) :
    Tab f' := by
  rw [hS0] at hS
  cases hS
  exact tab_of_tkeep (by unfold L0; omega) hw hw' hk hnt hT

theorem tab_sym {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSYM) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
  have hS0 := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (sym_step hw hL (X0 b.size om) hi.1.x_eq (by unfold X0; omega) hX4)
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
    simp (disch := omega) only [reqDecH, Finmap.lookup_insert_of_ne]) (by rw [hm]; decide) hT

theorem tab_lenx {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mLENX) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
  have hS0 := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (lenx_step hw hL (X0 b.size om) (f cACC) (f cPEND) hi.1.x_eq (by unfold X0; omega) hX4 rfl rfl)
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
    simp (disch := omega) only [reqDecH, Finmap.lookup_insert_of_ne]) (by rw [hm]; decide) hT

theorem tab_clput {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mCLPUT) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mCLPUT, clputN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mCLPUT, clputN) hmem (by decide)
  have hc := hi.2.cur
  rw [hm] at hc; simp only [facts, mCLPUT, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD] at hc; norm_num at hc
  obtain ⟨hf0, hf19, hfh, hh4, hhl, hhd⟩ := hc
  obtain ⟨o, ho⟩ : ∃ o, f (X0 b.size om + 134 + f cFILL) = o := ⟨_, rfl⟩
  have hor : 0 ≤ o ∧ o ≤ 18 := by
    rw [← ho, hi.1.ro _ (by omega) (by omega)]; exact order_rng b om lit _ hf0 hf19
  have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (clput_step hw hL (f cFILL) (X0 b.size om) b.size om (f cACC) o rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq rfl hf0 hf19
      (by omega) (by omega) ho (by omega) (by omega))
  exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
    simp (disch := omega) only [Finmap.lookup_insert_of_ne]) (by rw [hm]; decide) hT

theorem tab_symd {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSYMD) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mSYMD, symdN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSYMD, symdN) hmem (by decide)
  have hmr := hi.1.m_rng
  set s := f (X0 b.size om + 4) with hsd
  have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (symd_step hw hL (X0 b.size om) s (f cM) (f cOUTMAX) b.size (f cBF) (f (X0 b.size om + 16 + (s - 257)))
      (f (X0 b.size om + 45 + (s - 257))) hi.1.x_eq (by omega) (by omega) hsd.symm rfl rfl hi.1.n_eq rfl
      (fun _ hne => ⟨by omega, by omega⟩) rfl rfl)
  exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
    simp only [symdH, reqKH]
    split_ifs <;> simp (disch := omega) only [Finmap.lookup_insert_of_ne]) (by rw [hm]; decide) hT

theorem tab_lsym {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mLSYM) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mLSYM, lsymN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mLSYM, lsymN) hmem (by decide)
  have hr := hi.1.hdr_rng
  have hc := hi.2.cur
  rw [hm, facts_lsym] at hc
  obtain ⟨hf0, hflt, hhl, hhd, hs0⟩ := hc
  have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (lsym_step hw hL (X0 b.size om) (f (X0 b.size om + 4)) (f cFILL) b.size om
      (f (2080 + b.size + om + (f cFILL - 1))) hi.1.x_eq (by omega) (by omega) rfl rfl hi.1.n_eq hi.1.om_eq
      (fun _ => ⟨by omega, by omega⟩) (fun _ _ => ⟨by omega, by omega⟩) rfl)
  exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
    simp only [lsymH, reqH]
    split_ifs <;> simp (disch := omega) only [Finmap.lookup_insert_of_ne]) (by rw [hm]; decide) hT

theorem tab_decode {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDECODE) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hLn : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mDECODE, decodeN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDECODE, decodeN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  obtain ⟨hfr, hl1, hl15, hpair, hsane⟩ := hi.2.dec hm
  have ht02 : 0 ≤ f (X0 b.size om + 2) ∧ f (X0 b.size om + 2) ≤ 2 := by
    rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  by_cases hlt : f cBY < b.size
  · obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set l := f (X0 b.size om) with hld
    set t := f (X0 b.size om + 2) with htd
    set rt := f (X0 b.size om + 3) with hrtd
    set cv := f (X0 b.size om + 1) with hcvd
    set tb : Int := 2080 + (b.size : Int) + om + 337 + 352 * t with htbd
    have hs := hsane l hl1 hl15
    have htb : tbase b.size om t = tb := by rw [htbd]; unfold tbase LB0; ring
    rw [htb] at hs
    set bit := f (BT + (8 * (b[(f cBY).toNat]'(by omega) : Int) + ((f cBI).toNat : Int))) with hbitd
    have hS0 := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_step hw (f cBY).toNat (f cBI).toNat b.size (b[(f cBY).toNat]'(by omega)) om (X0 b.size om) l cv t rt bit tb
        (f (tb + 16 + l)) (f (tb + l)) (f (tb + 32 + l))
        (f (tb + 64 + f (tb + 32 + l) + (2 * cv + bit - f (tb + 16 + l)))) hLn (by omega) (by omega) hn hi.1.om_eq hi.1.x_eq
        (by omega) (by omega) hv hv8 rfl (by omega) (by omega) rfl rfl rfl rfl htbd.symm (by omega) (by omega) hl1 hl15
        rfl rfl rfl (fun hh => ⟨by omega, by omega⟩) rfl)
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp only [decH]
      split_ifs <;> simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT
  · have hS0 := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_trunc hw hL (f cBY) (f cBI) b.size om (X0 b.size om) rfl rfl hn hi.1.om_eq hi.1.x_eq (by omega))
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT

theorem tab_fixlens {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mFIXLENS) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mFIXLENS, fixlensN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mFIXLENS, fixlensN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hc := hi.2.cur
  rw [hm, facts_fixlens] at hc
  obtain ⟨hf0, hf318⟩ := hc
  obtain ⟨i, hi'⟩ : ∃ i : Nat, f cFILL = i := ⟨(f cFILL).toNat, by omega⟩
  by_cases hlt : i < 318
  · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (fixlens_step hw i b.size om (by unfold L0; omega) hi' hlt hi.1.n_eq hi.1.om_eq)
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT
  · have h318 : f cFILL = 318 := by omega
    have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (fixlens_end hw hL b.size om (f cLIT) (X0 b.size om) h318 hi.1.n_eq hi.1.om_eq rfl hi.1.x_eq (by omega) (by omega))
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT

theorem tab_clread {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mCLREAD) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mCLREAD, clreadN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mCLREAD, clreadN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hr := hi.1.hdr_rng
  have hc := hi.2.cur
  rw [hm, facts_clread] at hc
  obtain ⟨hf0, hf19, hh4, hhl, hhd⟩ := hc
  by_cases hlt : f cFILL < f cHCLEN
  · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (clread_req hw hL (f cFILL) (f cHCLEN) (X0 b.size om) b.size om rfl rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq hlt)
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp (disch := omega) only [reqH, Finmap.lookup_insert_of_ne]) hnt hT
  · by_cases h19 : f cFILL < 19
    · obtain ⟨o, ho⟩ : ∃ o, f (X0 b.size om + 134 + f cFILL) = o := ⟨_, rfl⟩
      have hor : 0 ≤ o ∧ o ≤ 18 := by
        rw [← ho, hi.1.ro _ (by omega) (by omega)]; exact order_rng b om lit _ hf0 h19
      have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (clread_zero hw hL (f cFILL) (f cHCLEN) (X0 b.size om) b.size om o rfl rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq hlt h19
          hf0 (by omega) (by omega) ho (by omega) (by omega))
      exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
        simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT
    · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (clread_end hw hL (f cFILL) (f cHCLEN) (X0 b.size om) b.size om rfl rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq hlt h19
          (by omega) (by omega))
      exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
        simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT

theorem tab_lens {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mLENS) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mLENS, lensN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mLENS, lensN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hr := hi.1.hdr_rng
  have hc := hi.2.cur
  rw [hm, facts_lens] at hc
  obtain ⟨hf0, hfl, hhl, hhd, hs0⟩ := hc
  by_cases hlt : f cFILL < f cHLIT + f cHDIST
  · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (lens_req hw hL (f cFILL) (f cHLIT) (f cHDIST) (X0 b.size om) b.size om rfl rfl rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq hlt
        (by omega) (by omega))
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      simp (disch := omega) only [reqDecH, Finmap.lookup_insert_of_ne]) hnt hT
  · obtain ⟨z, hz⟩ : ∃ z, f (2080 + (b.size : Int) + om + 256) = z := ⟨_, rfl⟩
    have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (lens_end hw hL (f cFILL) (f cHLIT) (f cHDIST) (X0 b.size om) b.size om z rfl rfl rfl hi.1.x_eq hi.1.n_eq hi.1.om_eq
        hlt (by omega) (by omega) (by omega) (by omega) hz)
    exact tab_of_stepH hw hS0 hS hw' (fun c h0 h1 => by
      split_ifs <;> simp (disch := omega) only [Finmap.lookup_insert_of_ne]) hnt hT

end VIRL5
