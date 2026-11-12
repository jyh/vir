/-
  O95, K5-2b: `Mag`, as DECLARATIONS-K5.md Addendum 4 declares it (vir 1871722), and the range wrappers of the modes that read
  a cell `Inv` leaves unbounded (SNLEN · LENX · DSTX · LREP here; DECODE and BUILD after). `Mag_step` (preservation) is owed and
  is NOT in this file: every wrapper here takes `Mag` as a hypothesis, and says so.
-/
import K5.Safe4

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

/-- The mode a READ returns to, or the mode itself (`InvM.read`'s reading). -/
def em (f : Int → Int) : Int := if f cMODE = mREAD then f cRET else f cMODE

/-- **`Mag`, Addendum 4's clauses P1–P4, D1, C1, B1, B2.** -/
structure Mag (n om : Nat) (f : Int → Int) : Prop where
  p1 : em f = mSNLEN → 0 ≤ f cPEND ∧ f cPEND ≤ 65535
  p2 : em f = mLENX → 0 ≤ f cPEND ∧ f cPEND ≤ 258
  p3 : em f = mDSTD ∨ em f = mDSTX ∨ (f cMODE = mDECODE ∧ f (X0 n om + 3) = mDSTD) → 0 ≤ f cPEND ∧ f cPEND ≤ 289
  p4 : em f = mLREP → 0 ≤ f cPEND ∧ f cPEND ≤ 11
  d1 : em f = mDSTX → 0 ≤ f cDIST ∧ f cDIST ≤ 24577
  c1 : f cMODE = mDECODE → 0 ≤ f (X0 n om + 1) ∧ f (X0 n om + 1) < 2 ^ (f (X0 n om)).toNat
  b1 : f cMODE = mBUILD → f cPHASE = 2 → 0 ≤ f cCODE ∧ f cCODE + 636 ≤ 636 * 2 ^ (f cINDEX).toNat
  b2 : f cMODE = mBUILD → f cPHASE = 3 → 0 ≤ f cLEFT ∧ f cLEFT ≤ 2 ^ (f cINDEX).toNat ∧
    0 ≤ f cREST ∧ f cREST ≤ 318 * f cINDEX ∧ 0 ≤ f cTOTAL ∧ f cTOTAL ≤ 318 * f cINDEX
  /-- Addendum 5's F1: every table's `first[l]` cell. -/
  f1 : ∀ t l : Int, 0 ≤ t → t ≤ 2 → 1 ≤ l → l ≤ 15 →
    0 ≤ f (tbase n om t + 16 + l) ∧ f (tbase n om t + 16 + l) ≤ 636 * 2 ^ 16

theorem em_of {f : Int → Int} {m : Int} (hm : f cMODE = m) (hr : m ≠ mREAD) : em f = m := by
  simp [em, hm, hr]

/-- At the initial world the mode is TABLE, so every clause is vacuous. -/
theorem Mag_init (b : Array Nat) (om : Nat) (lit : Bool) : Mag b.size om (initCell b om lit) := by
  have e0 : initCell b om lit cMODE = 0 :=
    initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have he : em (initCell b om lit) = 0 := by simp [em, e0, mREAD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (intros; simp_all [mSNLEN, mLENX, mDSTD, mDSTX, mLREP, mDECODE, mBUILD]; done)
  intro t l h0 h2 h1 h15
  rw [initCell_tail b om lit _ (by unfold tbase LB0; omega) (by unfold tbase LB0 X0; omega)]
  norm_num

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

theorem snlen_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hg : Mag b.size om f) (hm : f cMODE = mSNLEN) : SrcInRange (closeAt p snlenT, σ) := by
  have ha := acc_rng hi (by rw [hm]; decide)
  have hp := hg.p1 (em_of hm (by decide))
  have hmr := hi.1.m_rng
  have hbr := hi.1.by_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  apply snlen_step_inR hw (by unfold L0; omega) _ _ _ _ _ _ rfl rfl rfl hn rfl ho
  rclose

theorem lenx_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hg : Mag b.size om f) (hm : f cMODE = mLENX) : SrcInRange (closeAt p lenxT, σ) := by
  have ha := acc_rng hi (by rw [hm]; decide)
  have hp := hg.p2 (em_of hm (by decide))
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  apply lenx_step_inR hw (by unfold L0; omega) _ _ _ hx (by unfold X0; omega) (by rw [hL0]; unfold X0; omega) rfl rfl
  all_goals (try unfold X0)
  rclose

theorem dstx_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hg : Mag b.size om f) (hm : f cMODE = mDSTX) : SrcInRange (closeAt p dstxT, σ) := by
  have ha := acc_rng hi (by rw [hm]; decide)
  have he := em_of hm (by decide)
  have hp := hg.p3 (Or.inr (Or.inl he))
  have hd := hg.d1 he
  have hmr := hi.1.m_rng
  have ho := hi.1.om_eq
  apply dstx_step_inR hw (by unfold L0; omega) _ _ _ _ _ rfl rfl rfl rfl ho
  rclose

theorem lrep_inR (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mLREP) :
    SrcInRange (closeAt p lrepT, σ) := by
  have ha := acc_rng hi (by rw [hm]; decide)
  have hp := hg.p4 (em_of hm (by decide))
  have hc := hi.2.cur
  rw [hm, facts_lrep] at hc
  obtain ⟨hf0, hfh, hl286, hd30, _⟩ := hc
  have hh := hi.1.hdr_rng
  apply lrep_step_inR hw (by unfold L0; omega) _ _ _ _ _ rfl rfl rfl rfl rfl
  rclose

theorem decode_inR (hb : ∀ x ∈ b, x < 256) (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32)
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mDECODE) :
    SrcInRange (closeAt p decodeT, σ) := by
  have hLn : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hx := hi.1.x_eq
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  obtain ⟨_, hl1, hl15, hpair, hsane⟩ := hi.2.dec hm
  have ht02 : 0 ≤ f (X0 b.size om + 2) ∧ f (X0 b.size om + 2) ≤ 2 := by
    rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have hcv := hg.c1 hm
  have hp15 : (2 : Int) ^ (f (X0 b.size om)).toNat ≤ 32768 := by
    calc (2 : Int) ^ (f (X0 b.size om)).toNat ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32768 := by norm_num
  by_cases hlt : f cBY < b.size
  · obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set l := f (X0 b.size om) with hld
    set t := f (X0 b.size om + 2) with htd
    set tb : Int := 2080 + (b.size : Int) + om + 337 + 352 * t with htbd
    have hs := hsane l hl1 hl15
    have htb : tbase b.size om t = tb := by rw [htbd]; unfold tbase LB0; ring
    rw [htb] at hs
    have hF := hg.f1 t l ht02.1 ht02.2 hl1 hl15
    rw [htb] at hF
    have hbit := hi.1.bits (8 * (b[(f cBY).toNat]'(by omega) : Int) + ((f cBI).toNat : Int)) (by omega) (by omega)
      (Or.inl hnt)
    have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
    apply decode_step_inR hw (f cBY).toNat (f cBI).toNat b.size (b[(f cBY).toNat]'(by omega)) om (X0 b.size om) l
      (f (X0 b.size om + 1)) t (f (X0 b.size om + 3)) _ tb (f (tb + 16 + l)) (f (tb + l)) (f (tb + 32 + l)) _ hLn
      (by omega) (by omega) hn hi.1.om_eq hx (by omega) (by omega) hv hv8 rfl (by omega) (by rw [hL0]; omega) rfl rfl rfl rfl
      htbd.symm (by omega) (by rw [hL0]; omega) hl1 hl15 rfl rfl rfl (fun hh => ⟨by omega, by rw [hL0]; omega⟩) rfl
    all_goals (try rw [hX0])
    all_goals (have hcv' := hcv; rw [hX0] at hcv')
    all_goals (rcases hbit with hb0 | hb1)
    rclose
  · exact decode_trunc_inR hw (by unfold L0; omega) _ _ _ _ _ rfl rfl hn hi.1.om_eq hx (by omega)

end K5
