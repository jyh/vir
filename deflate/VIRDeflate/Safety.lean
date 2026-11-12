/-
OBJECT-DEFLATE under X1 (a): Safety's proof (STATUS-vir 293 (b); S-16), mode by mode. For each mode: its `stepS` (Fit.lean), its
result store as a World over an UPDATED cell function, and `Φ` (Measure.lean, written before this file) strictly decreasing.
The invariant `Inv` (S-16's conjuncts) is added here as the proofs reach each premise. This file grows per row.
-/
import VIRDeflate.Measure

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-- The cell function after a `READ` request of k bits returning to rt (`reqH`'s five stores). -/
def reqF (f : Int → Int) (k rt : Int) : Int → Int :=
  Function.update (Function.update (Function.update (Function.update (Function.update f 2068 k) 2069 0) 2070 1) 2071 rt) 0 2

theorem World.req {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2072 ≤ L) (k rt : Int) :
    World ⟨reqH σ.H p k rt, σ.R⟩ p L (reqF f k rt) := by
  unfold reqH reqF
  exact ((((hw.store (i := 2068) (by norm_num) (by omega)).store (i := 2069) (by norm_num) (by omega)).store (i := 2070)
    (by norm_num) (by omega)).store (i := 2071) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)

/-- The simp set that evaluates `Φ` on an updated cell function. -/
macro "phisimp" : tactic => `(tactic| simp [Φ, LOC, TBL, BITS, OUT, Function.update_apply, cMODE, cBY, cBI, cN, cM, cOUTMAX,
  cTB, cTI, cFILL, cPHASE, cINDEX, cX, cTGT, cHLIT, cHDIST, cHCLEN, cPEND, mTABLE, mHDR, mREAD, mHDRB, mHDRD, mSHDR, mFIXLENS,
  mDHDR, mSLEN, mSNLEN, mSCOPY, mBUILD, mLENS, mSYM, mDECODE, mSYMD, mLENX, mDSTD, mDSTX, mCOPY, mDH2, mDH3, mDH4, mCLREAD,
  mCLPUT, mLSYM, mLREP, mREP, mDONE, mREJECT])

/-- **HDR:** Φ drops (LOC 1 → READ's 0; nothing else moves). -/
theorem Φ_hdr {f : Int → Int} (hm : f cMODE = mHDR) : Φ (reqF f 1 3) < Φ f := by
  simp only [reqF]
  simp only [cMODE, mHDR] at hm
  phisimp
  simp [hm]

theorem safe_hdr {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hm : f cMODE = mHDR) :
    stepS p σ = some ⟨reqH σ.H p 1 3, σ.R⟩ ∧ World ⟨reqH σ.H p 1 3, σ.R⟩ p L (reqF f 1 3) ∧ Φ (reqF f 1 3) < Φ f :=
  ⟨stepS_hdr hw hL hm, hw.req (by omega) 1 3, Φ_hdr hm⟩

/-! ## The invariant, global part (S-16 conjuncts 1–3, mode validity, the dynamic header's ranges). The per-mode part and the
sane-table part are added as the per-mode proofs reach them. -/

/-- The 28 mode numbers, DONE and REJECT: a mode value outside this list would be a fixed point that is neither, and the
iteration would never end. -/
def validModes : List Int := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 98, 99]

/-- The modes a READ request returns to (reqN's and reqKN's `rt` arguments in Step.lean). -/
def readRets : List Int := [mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP]

structure InvG (b : Array Nat) (om : Nat) (lit : Bool) (f : Int → Int) : Prop where
  n_eq : f cN = b.size
  om_eq : f cOUTMAX = om
  x_eq : f cX = X0 b.size om
  lit_eq : f cLIT = (if lit then 1 else 0)
  input : ∀ i : Int, 2080 ≤ i → i < 2080 + b.size → f i = initCell b om lit i
  ro : ∀ i : Int, X0 b.size om + 16 ≤ i → i < X0 b.size om + 153 → f i = initCell b om lit i
  lens : ∀ j : Int, 0 ≤ j → j < 337 → 0 ≤ f (2080 + b.size + om + j) ∧ f (2080 + b.size + om + j) ≤ 15
  tb_rng : f cMODE = mTABLE → 0 ≤ f cTB ∧ f cTB < 256 ∧ 0 ≤ f cTI ∧ f cTI ≤ 7
  bits : ∀ c : Int, 0 ≤ c → c < 2048 → (f cMODE ≠ mTABLE ∨ c < 8 * f cTB + f cTI) → f (BT + c) = 0 ∨ f (BT + c) = 1
  by_rng : 0 ≤ f cBY ∧ f cBY ≤ b.size
  bi_rng : 0 ≤ f cBI ∧ f cBI ≤ 7
  by_end : f cBY = b.size → f cBI = 0
  m_rng : 0 ≤ f cM ∧ f cM ≤ om
  mode_ok : f cMODE ∈ validModes
  read_rt : f cMODE = mREAD → f cRET ∈ readRets
  hdr_rng : 0 ≤ f cHLIT ∧ f cHLIT ≤ 288 ∧ 0 ≤ f cHDIST ∧ f cHDIST ≤ 32 ∧ 0 ≤ f cHCLEN ∧ f cHCLEN ≤ 19

/-- A cell of the initial world that is none of n, OUTMAX, the flag, X, an input byte or the read-only area is 0. -/
theorem initCell_zero (b : Array Nat) (om : Nat) (lit : Bool) (i : Int) (h0 : 0 ≤ i) (h1 : i < 2080) (h15 : i ≠ 15)
    (h16 : i ≠ 16) (h17 : i ≠ 17) (h79 : i ≠ 2079) : initCell b om lit i = 0 := by
  simp only [initCell, X0]
  split_ifs <;> omega

/-- **Φ of the initial world is Safety's bound** `Nbound n OUTMAX`. -/
theorem Φ_init (b : Array Nat) (om : Nat) (lit : Bool) : Φ (initCell b om lit) = Nbound b.size om := by
  have e0 : initCell b om lit cMODE = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : initCell b om lit cBY = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e2 : initCell b om lit cBI = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e3 : initCell b om lit cM = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e18 : initCell b om lit cTB = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e19 : initCell b om lit cTI = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e15 : initCell b om lit cN = b.size := by simp [initCell, cN]
  have e16 : initCell b om lit cOUTMAX = om := by simp [initCell, cOUTMAX]
  simp only [Φ, TBL, BITS, OUT, LOC, Nbound, mW, e0, e1, e2, e3, e18, e19, e15, e16]
  simp [mTABLE, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD, mHDRD,
    mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]

/-! ## A READ request preserves the global invariant -/

theorem reqF_eq (f : Int → Int) (k rt i : Int) (hi : (i < 2068 ∧ i ≠ 0) ∨ 2071 < i) : reqF f k rt i = f i := by
  simp only [reqF, Function.update_apply]
  split_ifs <;> first | omega | rfl

theorem InvG.req {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) (hnt : f cMODE ≠ mTABLE)
    (k : Int) {rt : Int} (hrt : rt ∈ readRets) : InvG b om lit (reqF f k rt) where
  n_eq := by rw [reqF_eq _ _ _ _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [reqF_eq _ _ _ _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [reqF_eq _ _ _ _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [reqF_eq _ _ _ _ (by unfold cLIT; omega)]; exact h.lit_eq
  input i h1 h2 := by rw [reqF_eq _ _ _ _ (by omega)]; exact h.input i h1 h2
  ro i h1 h2 := by rw [reqF_eq _ _ _ _ (by unfold X0 at h1; omega)]; exact h.ro i h1 h2
  lens j h1 h2 := by rw [reqF_eq _ _ _ _ (by omega)]; exact h.lens j h1 h2
  tb_rng hm := by simp [reqF, cMODE, mTABLE] at hm
  bits c h1 h2 _ := by rw [reqF_eq _ _ _ _ (by unfold BT; omega)]; exact h.bits c h1 h2 (Or.inl hnt)
  by_rng := by rw [reqF_eq _ _ _ _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [reqF_eq _ _ _ _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [reqF_eq _ _ _ _ (by unfold cBY; omega), reqF_eq _ _ _ _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [reqF_eq _ _ _ _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by simp [reqF, cMODE, validModes]
  read_rt _ := by simpa [reqF, cRET, Function.update_apply] using hrt
  hdr_rng := by
    rw [reqF_eq _ _ _ _ (by unfold cHLIT; omega), reqF_eq _ _ _ _ (by unfold cHDIST; omega),
      reqF_eq _ _ _ _ (by unfold cHCLEN; omega)]
    exact h.hdr_rng

/-- **HDR, safe:** its `stepS`, the next world, the invariant kept, Φ lower. -/
theorem safe_hdr' {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {L : Nat} {f : Int → Int}
    (hw : World σ p L f) (hL : 2080 ≤ L) (hi : InvG b om lit f) (hm : f cMODE = mHDR) :
    stepS p σ = some ⟨reqH σ.H p 1 3, σ.R⟩ ∧ World ⟨reqH σ.H p 1 3, σ.R⟩ p L (reqF f 1 3) ∧
      InvG b om lit (reqF f 1 3) ∧ Φ (reqF f 1 3) < Φ f :=
  ⟨stepS_hdr hw hL hm, hw.req (by omega) 1 3, hi.req (by rw [hm]; decide) 1 (by decide), Φ_hdr hm⟩

/-! ## Scratch cells: the invariant says nothing about them -/

def scratch (i : Int) : Prop := i = 4 ∨ i = 5 ∨ i = 6 ∨ (10 ≤ i ∧ i ≤ 14) ∨ (2068 ≤ i ∧ i ≤ 2070) ∨ (2072 ≤ i ∧ i ≤ 2078)

theorem upd_eq (f : Int → Int) {i j : Int} (v : Int) (h : j ≠ i) : Function.update f i v j = f j :=
  Function.update_of_ne h v f

theorem InvG.upd {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {i : Int} (hs : scratch i)
    (v : Int) : InvG b om lit (Function.update f i v) := by
  unfold scratch at hs
  exact {
  n_eq := by rw [upd_eq _ _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [upd_eq _ _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [upd_eq _ _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [upd_eq _ _ (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun j h1 h2 => by rw [upd_eq _ _ (by omega)]; exact h.input j h1 h2
  ro := fun j h1 h2 => by rw [upd_eq _ _ (by unfold X0 at h1; omega)]; exact h.ro j h1 h2
  lens := fun j h1 h2 => by rw [upd_eq _ _ (by omega)]; exact h.lens j h1 h2
  tb_rng := fun hm => by
    rw [upd_eq _ _ (by unfold cMODE; omega)] at hm
    rw [upd_eq _ _ (by unfold cTB; omega), upd_eq _ _ (by unfold cTI; omega)]; exact h.tb_rng hm
  bits := fun c h1 h2 h3 => by
    rw [upd_eq _ _ (by unfold cMODE; omega), upd_eq _ _ (by unfold cTB; omega), upd_eq _ _ (by unfold cTI; omega)] at h3
    rw [upd_eq _ _ (by unfold BT; omega)]; exact h.bits c h1 h2 h3
  by_rng := by rw [upd_eq _ _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [upd_eq _ _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [upd_eq _ _ (by unfold cBY; omega), upd_eq _ _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [upd_eq _ _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [upd_eq _ _ (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [upd_eq _ _ (by unfold cMODE; omega)] at hm
    rw [upd_eq _ _ (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [upd_eq _ _ (by unfold cHLIT; omega), upd_eq _ _ (by unfold cHDIST; omega), upd_eq _ _ (by unfold cHCLEN; omega)]
    exact h.hdr_rng }

/-! ## The request modes -/

theorem safe_hdrb {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {L : Nat} {f : Int → Int}
    (hw : World σ p L f) (hL : 2080 ≤ L) (hi : InvG b om lit f) (hm : f cMODE = mHDRB) :
    stepS p σ = some ⟨reqH (σ.H.insert (p + 4) (f cACC)) p 2 4, σ.R⟩ ∧
      World ⟨reqH (σ.H.insert (p + 4) (f cACC)) p 2 4, σ.R⟩ p L (reqF (Function.update f 4 (f cACC)) 2 4) ∧
      InvG b om lit (reqF (Function.update f 4 (f cACC)) 2 4) ∧ Φ (reqF (Function.update f 4 (f cACC)) 2 4) < Φ f := by
  have hmem : (mHDRB, hdrbN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mHDRB, hdrbN) hmem (by decide)
  refine ⟨stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (hdrb_step hw hL (f cACC) rfl),
    (hw.store (i := 4) (by norm_num) (by omega)).req (by omega) 2 4,
    (hi.upd (by unfold scratch; omega) _).req (by rw [upd_eq _ _ (by unfold cMODE; omega), hm]; decide) 2 (by decide), ?_⟩
  simp only [reqF]
  simp only [cMODE, mHDRB] at hm
  phisimp
  simp [hm]

theorem safe_slen {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {L : Nat} {f : Int → Int}
    (hw : World σ p L f) (hL : 2080 ≤ L) (hi : InvG b om lit f) (hm : f cMODE = mSLEN) :
    stepS p σ = some ⟨reqH (σ.H.insert (p + 5) (f cACC)) p 16 9, σ.R⟩ ∧
      World ⟨reqH (σ.H.insert (p + 5) (f cACC)) p 16 9, σ.R⟩ p L (reqF (Function.update f 5 (f cACC)) 16 9) ∧
      InvG b om lit (reqF (Function.update f 5 (f cACC)) 16 9) ∧ Φ (reqF (Function.update f 5 (f cACC)) 16 9) < Φ f := by
  have hmem : (mSLEN, slenN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSLEN, slenN) hmem (by decide)
  refine ⟨stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (slen_step hw hL (f cACC) rfl),
    (hw.store (i := 5) (by norm_num) (by omega)).req (by omega) 16 9,
    (hi.upd (by unfold scratch; omega) _).req (by rw [upd_eq _ _ (by unfold cMODE; omega), hm]; decide) 16 (by decide), ?_⟩
  simp only [reqF]
  simp only [cMODE, mSLEN] at hm
  phisimp
  simp [hm]

theorem safe_dhdr {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {L : Nat} {f : Int → Int}
    (hw : World σ p L f) (hL : 2080 ≤ L) (hi : InvG b om lit f) (hm : f cMODE = mDHDR) :
    stepS p σ = some ⟨reqH σ.H p 5 20, σ.R⟩ ∧ World ⟨reqH σ.H p 5 20, σ.R⟩ p L (reqF f 5 20) ∧
      InvG b om lit (reqF f 5 20) ∧ Φ (reqF f 5 20) < Φ f := by
  have hmem : (mDHDR, dhdrN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDHDR, dhdrN) hmem (by decide)
  refine ⟨stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (dhdr_step hw hL), hw.req (by omega) 5 20,
    hi.req (by rw [hm]; decide) 5 (by decide), ?_⟩
  simp only [reqF]
  simp only [cMODE, mDHDR] at hm
  phisimp
  simp [hm]

end VIRDeflate.Step
