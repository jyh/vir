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

/-! ## The per-mode invariant (S-16 conjuncts 4–5), DEFINED before its proofs (design: STAGE-DEFLATE.md, "InvM") -/

/-- The lengths area's base, 2080 + n + OUTMAX (a constant of the world: InvG pins cells 15 and 16 to n and OUTMAX). -/
def LB0 (n om : Nat) : Int := 2080 + n + om
/-- Code table t's base: CL (0), L (1), D (2), each 352 cells (count 16 · first 16 · offset 16 · next 16 · syms 288). -/
def tbase (n om : Nat) (t : Int) : Int := LB0 n om + 337 + 352 * t

/-- A built table decodes inside itself: for every length, count and offset ≥ 0 with offset + count ≤ 288. -/
def sane (n om : Nat) (f : Int → Int) (t : Int) : Prop :=
  ∀ l : Int, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbase n om t + l) ∧ 0 ≤ f (tbase n om t + 32 + l) ∧
    f (tbase n om t + 32 + l) + f (tbase n om t + l) ≤ 288

/-- The field width a READ returning to md may fill, as 2^width. -/
def kcap (md : Int) : Int :=
  if md = mHDRB then 2 else if md = mHDRD then 4 else if md = mSLEN ∨ md = mSNLEN then 65536
  else if md = mDH2 ∨ md = mDH3 then 32 else if md = mDH4 then 16 else if md = mCLPUT then 8 else if md = mLENX then 32
  else if md = mDSTX then 8192 else if md = mLREP then 128 else 1

/-- #{j < k : length[sb + j] = l}. -/
def cnt (f : Int → Int) (sb l : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt f sb l k + (if f (sb + k) = l then 1 else 0)

/-- The sum of the counts of lengths 1 … l−1 (an offset). -/
def offOf (f : Int → Int) (tbb : Int) : Nat → Int
  | 0 => 0
  | l + 1 => offOf f tbb l + (if l = 0 then 0 else f (tbb + l))

/-- BUILD's invariant: its target and parameters, and the fold invariant of its phase. -/
def buildInv (n om : Nat) (f : Int → Int) : Prop :=
  let ph := f cPHASE
  let j := f cINDEX
  let X := X0 n om
  let sb := f (X + 5)
  let nn := f (X + 6)
  let tbb := f (X + 7)
  let tg := f cTGT
  let hl := f cHLIT
  let hd := f cHDIST
  0 ≤ tg ∧ tg ≤ 2 ∧ tbb = tbase n om tg ∧
  ((tg = 0 ∧ sb = LB0 n om + 318 ∧ nn = 19 ∧ hl ≤ 286 ∧ hd ≤ 30) ∨
   (tg = 1 ∧ sb = LB0 n om ∧ nn = hl ∧ hl + hd ≤ 318) ∨
   (tg = 2 ∧ sb = LB0 n om + hl ∧ nn = hd ∧ hl + hd ≤ 318 ∧ sane n om f 1)) ∧
  (ph = 0 → 0 ≤ j ∧ j ≤ 16 ∧ ∀ l : Int, 0 ≤ l → l < j → f (tbb + l) = 0) ∧
  (ph = 1 → 0 ≤ j ∧ j ≤ nn ∧ f tbb = 0 ∧ ∀ l : Int, 1 ≤ l → l ≤ 15 → f (tbb + l) = cnt f sb l j.toNat) ∧
  (2 ≤ ph → ph ≤ 3 → 1 ≤ j ∧ j ≤ 16 ∧ f tbb = 0 ∧ f (tbb + 32) = 0 ∧
    (∀ l : Int, 1 ≤ l → l ≤ 15 → f (tbb + l) = cnt f sb l nn.toNat) ∧
    (∀ l : Int, 1 ≤ l → l < (if ph = 2 then j else 16) → f (tbb + 32 + l) = offOf f tbb l.toNat ∧
      f (tbb + 48 + l) = offOf f tbb l.toNat)) ∧
  (ph = 4 → 0 ≤ j ∧ j ≤ nn ∧ sane n om f tg ∧
    ∀ l : Int, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbb + 48 + l) ∧ f (tbb + 48 + l) + (cnt f sb l nn.toNat - cnt f sb l j.toNat) ≤ 288) ∧
  (ph = 0 ∨ ph = 1 ∨ ph = 2 ∨ ph = 3 ∨ ph = 4)

/-- Each mode's own facts (no acc, no decoded symbol: those are `InvM.ret` and `InvM.sym`). -/
def facts (n om : Nat) (md : Int) (f : Int → Int) : Prop :=
  let fl := f cFILL
  let hl := f cHLIT
  let hd := f cHDIST
  let pd := f cPEND
  if md = mSNLEN then 0 ≤ pd
  else if md = mSCOPY then 0 ≤ pd ∧ f cM + pd ≤ f cOUTMAX
  else if md = mFIXLENS then 0 ≤ fl ∧ fl ≤ 318
  else if md = mBUILD then buildInv n om f
  else if md = mCLREAD then 0 ≤ fl ∧ fl ≤ 19 ∧ 4 ≤ f cHCLEN ∧ hl ≤ 286 ∧ hd ≤ 30
  else if md = mCLPUT then 0 ≤ fl ∧ fl < 19 ∧ fl < f cHCLEN ∧ 4 ≤ f cHCLEN ∧ hl ≤ 286 ∧ hd ≤ 30
  else if md = mLENS then 0 ≤ fl ∧ fl ≤ hl + hd ∧ hl ≤ 286 ∧ hd ≤ 30 ∧ sane n om f 0
  else if md = mLSYM then 0 ≤ fl ∧ fl < hl + hd ∧ hl ≤ 286 ∧ hd ≤ 30 ∧ sane n om f 0
  else if md = mLREP then 0 ≤ fl ∧ fl ≤ hl + hd ∧ hl ≤ 286 ∧ hd ≤ 30 ∧ sane n om f 0 ∧ 0 ≤ pd ∧ 0 ≤ f cLAST ∧ f cLAST ≤ 15
  else if md = mREP then 0 ≤ fl ∧ 0 ≤ pd ∧ fl + pd ≤ hl + hd ∧ hl ≤ 286 ∧ hd ≤ 30 ∧ sane n om f 0 ∧ 0 ≤ f cLAST ∧ f cLAST ≤ 15
  else if md = mSYM ∨ md = mSYMD then sane n om f 1 ∧ sane n om f 2
  else if md = mLENX ∨ md = mDSTD ∨ md = mDSTX then sane n om f 1 ∧ sane n om f 2 ∧ 0 ≤ pd
  else if md = mCOPY then sane n om f 1 ∧ sane n om f 2 ∧ 0 ≤ pd ∧ f cDIST ≤ f cM ∧ f cM + pd ≤ f cOUTMAX
  else True

/-- **The per-mode invariant.** -/
structure InvM (n om : Nat) (f : Int → Int) : Prop where
  syms : ∀ t q : Int, 0 ≤ t → t ≤ 2 → 0 ≤ q → q < 288 → 0 ≤ f (tbase n om t + 64 + q) ∧ f (tbase n om t + 64 + q) < 288
  cur : facts n om (f cMODE) f
  read : f cMODE = mREAD → facts n om (f cRET) f ∧ 1 ≤ f cK ∧ 1 ≤ f cWT ∧ 0 ≤ f cACC ∧ f cACC < f cWT ∧
    f cWT * 2 ^ (f cK).toNat ≤ kcap (f cRET)
  ret : f cMODE ∈ readRets → 0 ≤ f cACC ∧ f cACC < kcap (f cMODE)
  dec : f cMODE = mDECODE → facts n om (f (X0 n om + 3)) f ∧ 1 ≤ f (X0 n om) ∧ f (X0 n om) ≤ 15 ∧
    ((f (X0 n om + 2) = 0 ∧ f (X0 n om + 3) = mLSYM) ∨ (f (X0 n om + 2) = 1 ∧ f (X0 n om + 3) = mSYMD) ∨
     (f (X0 n om + 2) = 2 ∧ f (X0 n om + 3) = mDSTD)) ∧ sane n om f (f (X0 n om + 2))
  sym : f cMODE = mSYMD ∨ f cMODE = mDSTD ∨ f cMODE = mLSYM → 0 ≤ f (X0 n om + 4) ∧ f (X0 n om + 4) < 288
  scopy : f cMODE = mSCOPY → f cBY + f cPEND ≤ f cN
  ralign : f cMODE = mREAD → (f cRET = mSLEN ∨ f cRET = mSNLEN) → (f cBI + f cK) % 8 = 0
  align : f cMODE = mSLEN ∨ f cMODE = mSNLEN ∨ f cMODE = mSCOPY → f cBI = 0

/-- **Safety's invariant:** the global part and the per-mode part. -/
def Inv (b : Array Nat) (om : Nat) (lit : Bool) (f : Int → Int) : Prop := InvG b om lit f ∧ InvM b.size om f

/-! ## The initial world satisfies the invariant -/

theorem initCell_tail (b : Array Nat) (om : Nat) (lit : Bool) (i : Int) (h0 : 2080 + b.size ≤ i)
    (h1 : i < X0 b.size om + 16) : initCell b om lit i = 0 := by
  unfold initCell
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem Inv_init (b : Array Nat) (om : Nat) (lit : Bool) : Inv b om lit (initCell b om lit) := by
  have z : ∀ i : Int, 0 ≤ i → i < 2080 → i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 2079 → initCell b om lit i = 0 :=
    fun i a b' c d e g => initCell_zero b om lit i a b' c d e g
  have e15 : initCell b om lit cN = b.size := by simp [initCell, cN]
  have e16 : initCell b om lit cOUTMAX = om := by simp [initCell, cOUTMAX]
  have e0 : initCell b om lit cMODE = 0 := z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨{
    n_eq := e15
    om_eq := e16
    x_eq := by simp [initCell, cX]
    lit_eq := by simp [initCell, cLIT]
    input := fun _ _ _ => rfl
    ro := fun _ _ _ => rfl
    lens := fun j h1 h2 => by
      rw [initCell_tail b om lit _ (by omega) (by unfold X0; omega)]; omega
    tb_rng := fun _ => by
      rw [z cTB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        z cTI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega
    bits := fun c h1 h2 h3 => by
      rw [e0, z cTB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        z cTI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at h3
      simp [mTABLE] at h3; omega
    by_rng := by rw [z cBY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega
    bi_rng := by rw [z cBI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega
    by_end := fun _ => z cBI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    m_rng := by rw [z cM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega
    mode_ok := by rw [e0]; decide
    read_rt := fun h => by rw [e0] at h; simp [mREAD] at h
    hdr_rng := by
      rw [z cHLIT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        z cHDIST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        z cHCLEN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega }, {
    syms := fun t q h1 h2 h3 h4 => by
      simp only [tbase, LB0]
      rw [initCell_tail b om lit _ (by omega) (by unfold X0; omega)]; omega
    cur := by rw [e0]; simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM,
      mSYMD, mLENX, mDSTD, mDSTX, mCOPY]
    read := fun h => by rw [e0] at h; simp [mREAD] at h
    ret := fun h => by rw [e0] at h; simp [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
    dec := fun h => by rw [e0] at h; simp [mDECODE] at h
    sym := fun h => by rw [e0] at h; simp [mSYMD, mDSTD, mLSYM] at h
    scopy := fun h => by rw [e0] at h; simp [mSCOPY] at h
    ralign := fun h => by rw [e0] at h; simp [mREAD] at h
    align := fun h => by rw [e0] at h; simp [mSLEN, mSNLEN, mSCOPY] at h }⟩

/-! ## Safety from one safe step (the outer argument, checked before the 28 per-mode cases) -/

/-- What every non-terminal mode must give: its `stepS`, the next world, the invariant kept, and Φ strictly lower — OR the next
mode is DONE or REJECT (S-17: READ's and DECODE's truncation steps leave Φ unchanged). -/
def StepSafe : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int), (∀ x ∈ b, x < 256) →
    World σ p (L0 b.size om) f → Inv b om lit f → f cMODE ≠ mDONE → f cMODE ≠ mREJECT →
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT)

/-- Φ is never negative on a world satisfying the invariant. -/
def PhiNonneg : Prop := ∀ (b : Array Nat) (om : Nat) (lit : Bool) (f : Int → Int), Inv b om lit f → 0 ≤ Φ f

theorem modeOf_world {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) :
    modeOf p σ = f cMODE := by
  have h0 := hw.cell 0 (le_refl _) (by omega)
  rw [show p + 0 = p by omega] at h0
  simp [modeOf, h0, cMODE]

theorem iter_reach (hs : StepSafe) (hnn : PhiNonneg) (b : Array Nat) (om : Nat) (lit : Bool) (p : Int)
    (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int), World σ p (L0 b.size om) f → Inv b om lit f → Φ f < k →
      ∃ j σ', j ≤ k ∧ iterS p j σ = some σ' ∧ (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f _ hi hk
    have := hnn b om lit f hi
    push_cast at hk; omega
  | succ k ih =>
    intro σ f hw hi hk
    by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
    · exact ⟨0, σ, by omega, rfl, by rw [modeOf_world hw hL]; exact ht⟩
    · push Not at ht
      obtain ⟨σ', f', hst, hw', hi', hlt⟩ := hs b om lit p σ f hb hw hi ht.1 ht.2
      rcases hlt with hlt | ht'
      · obtain ⟨j, σ'', hj, hit, hm⟩ := ih σ' f' hw' hi' (by push_cast at hk ⊢; omega)
        exact ⟨j + 1, σ'', by omega, by simp [iterS, hst, hit], hm⟩
      · exact ⟨1, σ', by omega, by simp [iterS, hst], by rw [modeOf_world hw' hL]; exact ht'⟩

/-- **SAFETY, from one safe step and Φ ≥ 0:** with N = `Nbound` + 1 (S-17), a function of n and OUTMAX alone. -/
theorem safety_of_step (hs : StepSafe) (hnn : PhiNonneg) : SafetyStmt := by
  refine ⟨fun n om => Nbound n om + 1, fun b om lit p hb => ?_⟩
  obtain ⟨j, σ', hj, hit, hm⟩ := iter_reach hs hnn b om lit p hb (Nbound b.size om + 1) (initStore b om lit p)
    (initCell b om lit) (initStore_world b om lit p) (Inv_init b om lit) (by rw [Φ_init]; push_cast; omega)
  exact ⟨j, σ', hj, hit, hm⟩

/-! ## Φ ≥ 0 on the invariant -/

theorem build_nonneg {n om : Nat} {f : Int → Int} (hx : f cX = X0 n om) (hr : 0 ≤ f cHLIT ∧ f cHLIT ≤ 288 ∧ 0 ≤ f cHDIST ∧ f cHDIST ≤ 32 ∧ 0 ≤ f cHCLEN ∧ f cHCLEN ≤ 19)
    (hb : buildInv n om f) :
    0 ≤ bRem (f cPHASE) (f cINDEX) (f (f cX + 6)) +
      (if f cTGT = 0 then 1 + chainLD (f cHLIT) (f cHDIST) else if f cTGT = 1 then bfull (f cHDIST) + 1 else 1) := by
  rw [hx]
  obtain ⟨ht0, ht2, _, htg, h0, h1, h23, h4, hph⟩ := hb
  have hnn : 0 ≤ f (X0 n om + 6) := by
    rcases htg with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ <;> rw [h] <;> omega
  have hrem : 0 ≤ bRem (f cPHASE) (f cINDEX) (f (X0 n om + 6)) := by
    unfold bRem
    rcases hph with h | h | h | h | h
    · have := h0 h; simp [h]; omega
    · have := h1 h; simp [h]; omega
    · have := h23 (by omega) (by omega); simp [h]; omega
    · have := h23 (by omega) (by omega); simp [h]; omega
    · have := h4 h; simp [h]; omega
  have hcont : 0 ≤ (if f cTGT = 0 then 1 + chainLD (f cHLIT) (f cHDIST) else if f cTGT = 1 then bfull (f cHDIST) + 1 else 1) := by
    unfold chainLD bfull; split_ifs <;> omega
  omega

theorem LOC_nonneg {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (hg : InvG b om lit f) (hm : InvM b.size om f) :
    0 ≤ LOC f := by
  have hr := hg.hdr_rng
  by_cases hb : f cMODE = mBUILD
  · have hc := hm.cur
    rw [hb] at hc
    simp only [facts, mBUILD, mSNLEN, mSCOPY, mFIXLENS] at hc
    simp only [show ¬ ((11 : Int) = 9) by decide, show ¬ ((11 : Int) = 10) by decide, show ¬ ((11 : Int) = 6) by decide,
      if_false, if_true] at hc
    unfold LOC
    simp only [hb, mBUILD, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD,
      mHDRD, mFIXLENS]
    simp only [show ¬ ((11 : Int) = 1 ∨ (11 : Int) = 3 ∨ (11 : Int) = 5 ∨ (11 : Int) = 8 ∨ (11 : Int) = 7 ∨ (11 : Int) = 20 ∨
      (11 : Int) = 21 ∨ (11 : Int) = 13 ∨ (11 : Int) = 16) by decide,
      show ¬ ((11 : Int) = 15 ∨ (11 : Int) = 10 ∨ (11 : Int) = 19) by decide, show ¬ ((11 : Int) = 9 ∨ (11 : Int) = 18) by decide,
      show ¬ ((11 : Int) = 17) by decide, show ¬ ((11 : Int) = 4) by decide, show ¬ ((11 : Int) = 6) by decide, if_false, if_true]
    exact build_nonneg hg.x_eq hr hc
  · have hc := hm.cur
    have hmode := hg.mode_ok
    simp only [validModes, List.mem_cons, List.mem_nil_iff, or_false] at hmode
    rcases hmode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h <;> rw [h] at hc hb <;>
    simp [LOC, h, facts, bfull, chainLD, locFIX, locCL, mTABLE, mHDR, mREAD, mHDRB, mHDRD, mSHDR, mFIXLENS, mDHDR, mSLEN,
      mSNLEN, mSCOPY, mBUILD, mLENS, mSYM, mDECODE, mSYMD, mLENX, mDSTD, mDSTX, mCOPY, mDH2, mDH3, mDH4, mCLREAD, mCLPUT,
      mLSYM, mLREP, mREP, mDONE, mREJECT] at hc hb ⊢ <;>
    (try split_ifs) <;> omega

theorem Φ_nonneg : PhiNonneg := by
  intro b om lit f ⟨hg, hm⟩
  have hl := LOC_nonneg hg hm
  have hby := hg.by_rng
  have hbi := hg.bi_rng
  have hbe := hg.by_end
  have hmr := hg.m_rng
  have hn := hg.n_eq
  have hom := hg.om_eq
  have htbl : 0 ≤ TBL f := by
    unfold TBL; split_ifs with h
    · have := hg.tb_rng h; omega
    · omega
  have hbits : 0 ≤ BITS f := by
    unfold BITS
    by_cases he : f cBY = b.size
    · have := hbe he; omega
    · omega
  have hout : 0 ≤ OUT f := by unfold OUT; omega
  unfold Φ mW
  have : 0 ≤ TBL f + BITS f + OUT f := by omega
  positivity

/-- **SAFETY reduces to the 28 per-mode cases:** `StepSafe` alone. -/
theorem safety_of_stepSafe (hs : StepSafe) : SafetyStmt := safety_of_step hs Φ_nonneg

/-! ## Congruence: `facts` reads only the watched cells (cursor cells 1, 3, 5–13, 15, 16, 2074, and every cell from 2080 up) -/

def watched : List Int := [3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 2074]

def Watch (f g : Int → Int) : Prop := (∀ i : Int, 2080 ≤ i → f i = g i) ∧ ∀ c ∈ watched, f c = g c

theorem sane_congr {n om : Nat} {f g : Int → Int} (h : ∀ i : Int, 2080 ≤ i → f i = g i) {t : Int} (ht : 0 ≤ t)
    (hs : sane n om f t) : sane n om g t := by
  intro l h1 h2
  have a := h (tbase n om t + l) (by unfold tbase LB0; omega)
  have b := h (tbase n om t + 32 + l) (by unfold tbase LB0; omega)
  rw [← a, ← b]; exact hs l h1 h2

theorem cnt_congr {f g : Int → Int} (h : ∀ i : Int, 2080 ≤ i → f i = g i) {sb l : Int} (hsb : 2080 ≤ sb) :
    ∀ k : Nat, cnt f sb l k = cnt g sb l k
  | 0 => rfl
  | k + 1 => by simp only [cnt, cnt_congr h hsb k, h (sb + k) (by omega)]

theorem offOf_congr {f g : Int → Int} (h : ∀ i : Int, 2080 ≤ i → f i = g i) {tbb : Int} (htb : 2080 ≤ tbb) :
    ∀ l : Nat, offOf f tbb l = offOf g tbb l
  | 0 => rfl
  | l + 1 => by simp only [offOf, offOf_congr h htb l, h (tbb + l) (by omega)]

theorem buildInv_congr {n om : Nat} {f g : Int → Int} (hw : Watch f g) (hhl : 0 ≤ f cHLIT) (hb : buildInv n om f) :
    buildInv n om g := by
  obtain ⟨hi, hc⟩ := hw
  have hX : (2080 : Int) ≤ X0 n om := by unfold X0; omega
  have e5 := hi (X0 n om + 5) (by omega)
  have e6 := hi (X0 n om + 6) (by omega)
  have e7 := hi (X0 n om + 7) (by omega)
  have e12 := hc 12 (by decide)
  have e13 := hc 13 (by decide)
  have e74 := hc 2074 (by decide)
  have e7c := hc 7 (by decide)
  have e8c := hc 8 (by decide)
  unfold buildInv at hb ⊢
  simp only [cPHASE, cINDEX, cTGT, cHLIT, cHDIST] at hb ⊢ hhl
  rw [← e5, ← e6, ← e7, ← e12, ← e13, ← e74, ← e7c, ← e8c]
  obtain ⟨ht0, ht2, htb, htg, h0, h1, h23, h4, hph⟩ := hb
  have htb2 : (2080 : Int) ≤ f (X0 n om + 7) := by rw [htb]; unfold tbase LB0; omega
  have hsb : (2080 : Int) ≤ f (X0 n om + 5) := by
    rcases htg with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> rw [h] <;> unfold LB0 <;> omega
  have hcnt : ∀ (l : Int) (k : Nat), cnt f (f (X0 n om + 5)) l k = cnt g (f (X0 n om + 5)) l k :=
    fun l k => cnt_congr hi (l := l) hsb k
  have hoff := offOf_congr hi htb2
  refine ⟨ht0, ht2, htb, ?_, ?_, ?_, ?_, ?_, hph⟩
  · rcases htg with h | h | ⟨a, b', c, d, e⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, b', c, d, sane_congr hi (by norm_num) e⟩)
  · intro hp
    obtain ⟨a, b', c⟩ := h0 hp
    exact ⟨a, b', fun l l0 lj => by rw [← hi _ (by omega)]; exact c l l0 lj⟩
  · intro hp
    obtain ⟨a, b', c, d⟩ := h1 hp
    refine ⟨a, b', by rw [← hi _ htb2]; exact c, fun l l1 l15 => ?_⟩
    rw [← hi _ (by omega), ← hcnt]; exact d l l1 l15
  · intro hp2 hp3
    obtain ⟨a, b', c, d, e, g'⟩ := h23 hp2 hp3
    refine ⟨a, b', by rw [← hi _ htb2]; exact c, by rw [← hi _ (by omega)]; exact d, fun l l1 l15 => ?_, fun l l1 lj => ?_⟩
    · rw [← hi _ (by omega), ← hcnt]; exact e l l1 l15
    · rw [← hi _ (by omega), ← hi _ (by omega), ← hoff]; exact g' l l1 lj
  · intro hp
    obtain ⟨a, b', c, d⟩ := h4 hp
    refine ⟨a, b', sane_congr hi ht0 c, fun l l1 l15 => ?_⟩
    rw [← hi _ (by omega), ← hcnt, ← hcnt]; exact d l l1 l15

theorem ite_imp {c : Prop} [Decidable c] {a b a' b' : Prop} (h1 : a → a') (h2 : b → b') :
    (if c then a else b) → (if c then a' else b') := by
  split_ifs <;> assumption

theorem facts_congr {n om : Nat} {f g : Int → Int} (hw : Watch f g) (hhl : 0 ≤ f cHLIT) {md : Int}
    (hf : facts n om md f) : facts n om md g := by
  have hb := fun h => buildInv_congr (n := n) (om := om) hw hhl h
  obtain ⟨hi, hc⟩ := hw
  have s0 := sane_congr (n := n) (om := om) hi (t := 0) (le_refl _)
  have s1 := sane_congr (n := n) (om := om) hi (t := 1) (by norm_num)
  have s2 := sane_congr (n := n) (om := om) hi (t := 2) (by norm_num)
  have e3 : f cM = g cM := hc cM (by decide)
  have e5 : f cPEND = g cPEND := hc cPEND (by decide)
  have e6 : f cDIST = g cDIST := hc cDIST (by decide)
  have e7 : f cHLIT = g cHLIT := hc cHLIT (by decide)
  have e8 : f cHDIST = g cHDIST := hc cHDIST (by decide)
  have e9 : f cHCLEN = g cHCLEN := hc cHCLEN (by decide)
  have e10 : f cFILL = g cFILL := hc cFILL (by decide)
  have e11 : f cLAST = g cLAST := hc cLAST (by decide)
  have e15 : f cN = g cN := hc cN (by decide)
  have e16 : f cOUTMAX = g cOUTMAX := hc cOUTMAX (by decide)
  unfold facts at hf ⊢
  rw [← e3, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e16]
  revert hf
  repeat' (first | apply ite_imp | (intro h; tauto))

/-! ## A READ request keeps the per-mode invariant -/

theorem watch_reqF (f : Int → Int) (k rt : Int) : Watch f (reqF f k rt) := by
  refine ⟨fun i hi => (reqF_eq f k rt i (by omega)).symm, fun c hc => ?_⟩
  simp only [watched, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rw [reqF_eq f k rt c (by omega)]

theorem watch_upd (f : Int → Int) {i : Int} (hi : i < 2080) (hw : i ∉ watched) (v : Int) : Watch f (Function.update f i v) := by
  refine ⟨fun j hj => (upd_eq f v (by omega)).symm, fun c hc => ?_⟩
  rw [upd_eq f v (by rintro rfl; exact hw hc)]

def SymsOK (n om : Nat) (f : Int → Int) : Prop :=
  ∀ t q : Int, 0 ≤ t → t ≤ 2 → 0 ≤ q → q < 288 → 0 ≤ f (tbase n om t + 64 + q) ∧ f (tbase n om t + 64 + q) < 288

theorem SymsOK.upd {n om : Nat} {f : Int → Int} (h : SymsOK n om f) {i : Int} (hi : i < 2080) (v : Int) :
    SymsOK n om (Function.update f i v) := by
  intro t q h1 h2 h3 h4
  rw [upd_eq f v (by unfold tbase LB0; omega)]; exact h t q h1 h2 h3 h4

theorem InvM.req {n om : Nat} {f : Int → Int} (h : SymsOK n om f) (hhl : 0 ≤ f cHLIT) {k rt : Int}
    (hf : facts n om rt f) (hk : 1 ≤ k) (hcap : 2 ^ k.toNat ≤ kcap rt)
    (hal : rt = mSLEN ∨ rt = mSNLEN → (f cBI + k) % 8 = 0) : InvM n om (reqF f k rt) where
  syms t q h1 h2 h3 h4 := by
    rw [reqF_eq f k rt _ (by unfold tbase LB0; omega)]; exact h t q h1 h2 h3 h4
  cur := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]]
    simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD,
      mDSTX, mCOPY]
  read _ := by
    have hr : reqF f k rt cRET = rt := by simp [reqF, cRET, Function.update_apply]
    have hK : reqF f k rt cK = k := by simp [reqF, cK, Function.update_apply]
    have hA : reqF f k rt cACC = 0 := by simp [reqF, cACC, Function.update_apply]
    have hW : reqF f k rt cWT = 1 := by simp [reqF, cWT, Function.update_apply]
    rw [hr, hK, hA, hW]
    exact ⟨facts_congr (watch_reqF f k rt) hhl hf, hk, le_refl _, le_refl _, by norm_num, by simpa using hcap⟩
  ret hm := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]] at hm
    simp [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at hm
  dec hm := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]] at hm; simp [mDECODE] at hm
  sym hm := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]] at hm; simp [mSYMD, mDSTD, mLSYM] at hm
  scopy hm := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]] at hm; simp [mSCOPY] at hm
  ralign _ hr := by
    rw [show reqF f k rt cRET = rt by simp [reqF, cRET, Function.update_apply]] at hr
    rw [show reqF f k rt cBI = f cBI from reqF_eq f k rt _ (by unfold cBI; omega),
      show reqF f k rt cK = k by simp [reqF, cK, Function.update_apply]]
    exact hal hr
  align hm := by
    rw [show reqF f k rt cMODE = 2 by simp [reqF, cMODE]] at hm; simp [mSLEN, mSNLEN, mSCOPY] at hm

/-- A write to a cell below 2080 that no part of the invariant watches keeps `InvM`, unless it is the mode or a cell the
mode's READ/DECODE relation reads (0, 2068–2071, and X's cells are ≥ 2080). -/
theorem InvM.upd {n om : Nat} {f : Int → Int} (h : InvM n om f) (hhl : 0 ≤ f cHLIT) {i : Int} (hi : i < 2080)
    (hw : i ∉ watched) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (hr : i < 2068 ∨ 2071 < i) (v : Int) : InvM n om (Function.update f i v) := by
  have W := watch_upd f hi hw v
  have u : ∀ c : Int, c ≠ i → Function.update f i v c = f c := fun c hc => upd_eq f v hc
  have hm : Function.update f i v cMODE = f cMODE := u _ (by unfold cMODE; omega)
  exact {
  syms := fun t q h1 h2 h3 h4 => by rw [u _ (by unfold tbase LB0; omega)]; exact h.syms t q h1 h2 h3 h4
  cur := by rw [hm]; exact facts_congr W hhl h.cur
  read := fun hm' => by
    rw [hm] at hm'
    obtain ⟨a, b, c, d, e, g⟩ := h.read hm'
    rw [u cRET (by unfold cRET; omega), u cK (by unfold cK; omega), u cWT (by unfold cWT; omega), u cACC (by unfold cACC; omega)]
    exact ⟨facts_congr W hhl a, b, c, d, e, g⟩
  ret := fun hm' => by
    rw [hm] at hm' ⊢; rw [u cACC (by unfold cACC; omega)]; exact h.ret hm'
  dec := fun hm' => by
    rw [hm] at hm'
    obtain ⟨a, b, c, d, e⟩ := h.dec hm'
    have hX : (2080 : Int) ≤ X0 n om := by unfold X0; omega
    rw [u (X0 n om + 3) (by omega), u (X0 n om) (by omega), u (X0 n om + 2) (by omega)]
    refine ⟨facts_congr W hhl a, b, c, d, ?_⟩
    rcases d with ⟨d1, _⟩ | ⟨d1, _⟩ | ⟨d1, _⟩ <;> rw [d1] at e ⊢ <;> exact sane_congr W.1 (by norm_num) e
  sym := fun hm' => by
    rw [hm] at hm'
    have hX : (2080 : Int) ≤ X0 n om := by unfold X0; omega
    rw [u (X0 n om + 4) (by omega)]; exact h.sym hm'
  scopy := fun hm' => by
    rw [hm] at hm'
    rw [u cBY (by unfold cBY; omega), u cPEND (by unfold cPEND; intro e; exact hw (by rw [← e]; decide)),
      u cN (by unfold cN; intro e; exact hw (by rw [← e]; decide))]
    exact h.scopy hm'
  ralign := fun hm' hr' => by
    rw [hm] at hm'; rw [u cRET (by unfold cRET; omega)] at hr'
    rw [u cBI (by unfold cBI; omega), u cK (by unfold cK; omega)]; exact h.ralign hm' hr'
  align := fun hm' => by
    rw [hm] at hm'; rw [u cBI (by unfold cBI; omega)]; exact h.align hm' }

/-! ## The request modes, with the full invariant -/

theorem safeI_hdr {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mHDR) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ Φ f' < Φ f := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨a, b', c, d⟩ := safe_hdr' (b := b) (om := om) (lit := lit) hw hL hi.1 hm
  exact ⟨_, _, a, b', ⟨c, InvM.req hi.2.syms hi.1.hdr_rng.1 (by simp [facts, mHDRB, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT,
    mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mHDRB]) (fun h => by simp [mHDRB, mSLEN, mSNLEN] at h)⟩, d⟩

theorem safeI_dhdr {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDHDR) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ Φ f' < Φ f := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨a, b', c, d⟩ := safe_dhdr (b := b) (om := om) (lit := lit) hw hL hi.1 hm
  exact ⟨_, _, a, b', ⟨c, InvM.req hi.2.syms hi.1.hdr_rng.1 (by simp [facts, mDH2, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT,
    mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mDH2, mHDRB, mHDRD,
    mSLEN, mSNLEN]) (fun h => by simp [mDH2, mSLEN, mSNLEN] at h)⟩, d⟩

theorem safeI_hdrb {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mHDRB) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ Φ f' < Φ f := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨a, b', c, d⟩ := safe_hdrb (b := b) (om := om) (lit := lit) hw hL hi.1 hm
  have hu := SymsOK.upd (n := b.size) (om := om) hi.2.syms (i := 4) (by norm_num) (f cACC)
  exact ⟨_, _, a, b', ⟨c, InvM.req hu (by rw [upd_eq _ _ (by unfold cHLIT; omega)]; exact hi.1.hdr_rng.1)
    (by simp [facts, mHDRD, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX,
      mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mHDRD, mHDRB]) (fun h => by simp [mHDRD, mSLEN, mSNLEN] at h)⟩, d⟩

theorem safeI_slen {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSLEN) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ Φ f' < Φ f := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨a, b', c, d⟩ := safe_slen (b := b) (om := om) (lit := lit) hw hL hi.1 hm
  have hacc := hi.2.ret (by rw [hm]; decide)
  have hu := SymsOK.upd (n := b.size) (om := om) hi.2.syms (i := 5) (by norm_num) (f cACC)
  exact ⟨_, _, a, b', ⟨c, InvM.req hu (by rw [upd_eq _ _ (by unfold cHLIT; omega)]; exact hi.1.hdr_rng.1)
    (by simp [facts, mSNLEN, cPEND]; exact hacc.1) (by norm_num)
    (by simp [kcap, mSNLEN, mSLEN, mHDRB, mHDRD])
    (fun _ => by rw [upd_eq _ _ (by unfold cBI; omega), hi.2.align (Or.inl hm)]; norm_num)⟩, d⟩

/-! ## Helpers for READ: the mode cell, the cursor's carry, a terminal mode, the input bytes -/

theorem InvG.mode {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {v : Int}
    (hv : v ∈ validModes) (hv0 : v ≠ mTABLE) (hvr : v = mREAD → f cRET ∈ readRets) (hnt : f cMODE ≠ mTABLE) :
    InvG b om lit (Function.update f 0 v) := by
  have u : ∀ c : Int, c ≠ 0 → Function.update f 0 v c = f c := fun c hc => upd_eq f v hc
  have hm : Function.update f 0 v cMODE = v := by simp [cMODE]
  exact {
  n_eq := by rw [u _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun i h1 h2 => by rw [u _ (by omega)]; exact h.input i h1 h2
  ro := fun i h1 h2 => by rw [u _ (by unfold X0 at h1; omega)]; exact h.ro i h1 h2
  lens := fun j h1 h2 => by rw [u _ (by omega)]; exact h.lens j h1 h2
  tb_rng := fun hm' => by rw [hm] at hm'; exact absurd hm' hv0
  bits := fun c h1 h2 _ => by rw [u _ (by unfold BT; omega)]; exact h.bits c h1 h2 (Or.inl hnt)
  by_rng := by rw [u _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [u _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [u _ (by unfold cBY; omega), u _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [u _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [hm]; exact hv
  read_rt := fun hm' => by rw [hm] at hm'; rw [u _ (by unfold cRET; omega)]; exact hvr hm'
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega), u _ (by unfold cHCLEN; omega)]; exact h.hdr_rng }

/-- Into DONE or REJECT: every per-mode conjunct is vacuous or untouched. -/
theorem InvM.term {n om : Nat} {f : Int → Int} (h : SymsOK n om f) {v : Int} (hv : v = mDONE ∨ v = mREJECT) :
    InvM n om (Function.update f 0 v) := by
  have hm : Function.update f 0 v cMODE = v := by simp [cMODE]
  rcases hv with rfl | rfl <;> exact {
    syms := fun t q h1 h2 h3 h4 => by rw [upd_eq f _ (by unfold tbase LB0; omega)]; exact h t q h1 h2 h3 h4
    cur := by rw [hm]; simp [facts, mDONE, mREJECT, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP,
      mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY]
    read := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mREAD] at hm'
    ret := fun hm' => by
      rw [hm] at hm'; simp [mDONE, mREJECT, readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX,
        mLREP] at hm'
    dec := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mDECODE] at hm'
    sym := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mSYMD, mDSTD, mLSYM] at hm'
    scopy := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mSCOPY] at hm'
    ralign := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mREAD] at hm'
    align := fun hm' => by rw [hm] at hm'; simp [mDONE, mREJECT, mSLEN, mSNLEN, mSCOPY] at hm' }

theorem InvM.syms_ok {n om : Nat} {f : Int → Int} (h : InvM n om f) : SymsOK n om f := h.syms

/-- An input byte is the byte string's, and below 256. -/
theorem InvG.byte {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) (hb : ∀ x ∈ b, x < 256)
    (j : Nat) (hj : j < b.size) : f (IN + j) = (b[j] : Int) ∧ b[j] < 256 := by
  refine ⟨?_, hb _ (Array.getElem_mem hj)⟩
  rw [h.input (IN + j) (by unfold IN; omega) (by unfold IN; omega)]
  unfold initCell IN
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp [Array.getD, hj]

/-- READ's cursor advance keeps InvG: (bx, bi) → tblNext bx bi, with bx < n. -/
theorem InvG.cursor {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {bx bi : Int}
    (hby : f cBY = bx) (hbi : f cBI = bi) (hbx : bx < b.size) :
    InvG b om lit (Function.update (Function.update f 1 (tblNext bx bi).1) 2 (tblNext bx bi).2) := by
  have u : ∀ c : Int, c ≠ 1 → c ≠ 2 → Function.update (Function.update f 1 (tblNext bx bi).1) 2 (tblNext bx bi).2 c = f c :=
    fun c h1 h2 => by rw [upd_eq _ _ h2, upd_eq _ _ h1]
  have e1 : Function.update (Function.update f 1 (tblNext bx bi).1) 2 (tblNext bx bi).2 cBY = (tblNext bx bi).1 := by
    simp [cBY]
  have e2 : Function.update (Function.update f 1 (tblNext bx bi).1) 2 (tblNext bx bi).2 cBI = (tblNext bx bi).2 := by
    simp [cBI]
  have hbr := h.by_rng
  have hir := h.bi_rng
  rw [hby] at hbr; rw [hbi] at hir
  exact {
  n_eq := by rw [u _ (by unfold cN; omega) (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega) (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega) (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun i h1 h2 => by rw [u _ (by omega) (by omega)]; exact h.input i h1 h2
  ro := fun i h1 h2 => by rw [u _ (by unfold X0 at h1; omega) (by unfold X0 at h1; omega)]; exact h.ro i h1 h2
  lens := fun j h1 h2 => by rw [u _ (by omega) (by omega)]; exact h.lens j h1 h2
  tb_rng := fun hm => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cTB; omega) (by unfold cTB; omega), u _ (by unfold cTI; omega) (by unfold cTI; omega)]
    exact h.tb_rng hm
  bits := fun c h1 h2 h3 => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega), u _ (by unfold cTB; omega) (by unfold cTB; omega),
      u _ (by unfold cTI; omega) (by unfold cTI; omega)] at h3
    rw [u _ (by unfold BT; omega) (by unfold BT; omega)]; exact h.bits c h1 h2 h3
  by_rng := by rw [e1]; unfold tblNext; split_ifs <;> simp <;> omega
  bi_rng := by rw [e2]; unfold tblNext; split_ifs <;> simp <;> omega
  by_end := by rw [e1, e2]; unfold tblNext; split_ifs <;> simp <;> omega
  m_rng := by rw [u _ (by unfold cM; omega) (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cRET; omega) (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega) (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega) (by unfold cHDIST; omega),
      u _ (by unfold cHCLEN; omega) (by unfold cHCLEN; omega)]; exact h.hdr_rng }

theorem Watch.trans {f g h : Int → Int} (a : Watch f g) (b : Watch g h) : Watch f h :=
  ⟨fun i hi => (a.1 i hi).trans (b.1 i hi), fun c hc => (a.2 c hc).trans (b.2 c hc)⟩

/-! ## LOC < W on the invariant (so a step that lowers the W-part may raise LOC to anything it reaches) -/

theorem build_lt {n om : Nat} {f : Int → Int} (hx : f cX = X0 n om) (hr : 0 ≤ f cHLIT ∧ f cHLIT ≤ 288 ∧ 0 ≤ f cHDIST ∧
    f cHDIST ≤ 32 ∧ 0 ≤ f cHCLEN ∧ f cHCLEN ≤ 19) (hb : buildInv n om f) :
    bRem (f cPHASE) (f cINDEX) (f (f cX + 6)) +
      (if f cTGT = 0 then 1 + chainLD (f cHLIT) (f cHDIST) else if f cTGT = 1 then bfull (f cHDIST) + 1 else 1) < 4096 := by
  rw [hx]
  obtain ⟨ht0, ht2, _, htg, h0, h1, h23, h4, hph⟩ := hb
  have hnn : f (X0 n om + 6) ≤ 288 := by
    rcases htg with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ <;> rw [h] <;> omega
  have hnn0 : 0 ≤ f (X0 n om + 6) := by
    rcases htg with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ <;> rw [h] <;> omega
  have hrem : bRem (f cPHASE) (f cINDEX) (f (X0 n om + 6)) ≤ 700 := by
    unfold bRem
    rcases hph with h | h | h | h | h
    · have := h0 h; simp [h]; omega
    · have := h1 h; simp [h]; omega
    · have := h23 (by omega) (by omega); simp [h]; omega
    · have := h23 (by omega) (by omega); simp [h]; omega
    · have := h4 h; simp [h]; omega
  have hcont : (if f cTGT = 0 then 1 + chainLD (f cHLIT) (f cHDIST) else if f cTGT = 1 then bfull (f cHDIST) + 1 else 1) ≤ 1000 := by
    unfold chainLD bfull; split_ifs <;> omega
  omega

theorem LOC_lt {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (hg : InvG b om lit f) (hm : InvM b.size om f) :
    LOC f < 4096 := by
  have hr := hg.hdr_rng
  by_cases hb : f cMODE = mBUILD
  · have hc := hm.cur
    rw [hb] at hc
    simp only [facts, mBUILD, mSNLEN, mSCOPY, mFIXLENS] at hc
    simp only [show ¬ ((11 : Int) = 9) by decide, show ¬ ((11 : Int) = 10) by decide, show ¬ ((11 : Int) = 6) by decide,
      if_false, if_true] at hc
    unfold LOC
    simp only [hb, mBUILD, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD,
      mHDRD, mFIXLENS]
    simp only [show ¬ ((11 : Int) = 1 ∨ (11 : Int) = 3 ∨ (11 : Int) = 5 ∨ (11 : Int) = 8 ∨ (11 : Int) = 7 ∨ (11 : Int) = 20 ∨
      (11 : Int) = 21 ∨ (11 : Int) = 13 ∨ (11 : Int) = 16) by decide,
      show ¬ ((11 : Int) = 15 ∨ (11 : Int) = 10 ∨ (11 : Int) = 19) by decide, show ¬ ((11 : Int) = 9 ∨ (11 : Int) = 18) by decide,
      show ¬ ((11 : Int) = 17) by decide, show ¬ ((11 : Int) = 4) by decide, show ¬ ((11 : Int) = 6) by decide, if_false, if_true]
    exact build_lt hg.x_eq hr hc
  · have hc := hm.cur
    have hmode := hg.mode_ok
    simp only [validModes, List.mem_cons, List.mem_nil_iff, or_false] at hmode
    rcases hmode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h <;> rw [h] at hc hb <;>
    simp [LOC, h, facts, bfull, chainLD, locFIX, locCL, mTABLE, mHDR, mREAD, mHDRB, mHDRD, mSHDR, mFIXLENS, mDHDR, mSLEN,
      mSNLEN, mSCOPY, mBUILD, mLENS, mSYM, mDECODE, mSYMD, mLENX, mDSTD, mDSTX, mCOPY, mDH2, mDH3, mDH4, mCLREAD, mCLPUT,
      mLSYM, mLREP, mREP, mDONE, mREJECT] at hc hb ⊢ <;>
    (try split_ifs) <;> omega

/-! ## READ -/

theorem pow_toNat_succ (k : Int) (hk : 1 ≤ k) : (2 : Int) ^ k.toNat = 2 * 2 ^ (k - 1).toNat := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, k = (m : Int) + 1 := ⟨(k - 1).toNat, by omega⟩
  rw [show ((m : Int) + 1).toNat = m + 1 by omega, show ((m : Int) + 1 - 1).toNat = m by omega, pow_succ]; ring

theorem safeI_read {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} (hb : ∀ x ∈ b, x < 256)
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mREAD) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mREAD, readN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mREAD, readN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hhl := hi.1.hdr_rng.1
  by_cases hlt : f cBY < b.size
  · -- a bit remains
    obtain ⟨hfr, hk1, hw1, ha0, hal, hcap⟩ := hi.2.read hm
    have hrt := hi.1.read_rt hm
    obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have ht01 := hi.1.bits (8 * (b[(f cBY).toNat]'(by omega) : Int) + f cBI) (by omega) (by omega) (Or.inl hnt)
    have hstep := readbit_step hw (f cBY).toNat (f cBI).toNat b.size (b[(f cBY).toNat]'(by omega)) (f cK) (f cACC) (f cWT)
      (f cRET) (f (BT + (8 * (b[(f cBY).toNat]'(by omega) : Int) + f cBI))) hL (by omega) (by omega) hn (by omega) (by omega)
      hv hv8 (by rw [hbiE]) rfl rfl rfl rfl
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2 hstep
    simp only [show ((f cBY).toNat : Int) = f cBY by omega, show ((f cBI).toNat : Int) = f cBI by omega] at hS
    set t := f (BT + (8 * (b[(f cBY).toNat]'(by omega) : Int) + f cBI)) with ht
    set f1 := Function.update (Function.update (Function.update (Function.update (Function.update f 1 (tblNext (f cBY) (f cBI)).1)
      2 (tblNext (f cBY) (f cBI)).2) 2069 (f cACC + t * f cWT)) 2070 (2 * f cWT)) 2068 (f cK - 1) with hf1
    have hw1' : World ⟨rdH σ.H p (f cBY) (f cBI) (f cACC) (f cWT) (f cK) t, σ.R⟩ p (L0 b.size om) f1 := by
      unfold rdH
      exact ((((hw.store (i := 1) (by norm_num) (by unfold L0; omega)).store (i := 2) (by norm_num) (by unfold L0; omega)).store
        (i := 2069) (by norm_num) (by unfold L0; omega)).store (i := 2070) (by norm_num) (by unfold L0; omega)).store
        (i := 2068) (by norm_num) (by unfold L0; omega)
    have hg1 : InvG b om lit f1 :=
      (((hi.1.cursor rfl rfl hlt).upd (by unfold scratch; omega) _).upd (by unfold scratch; omega) _).upd
        (by unfold scratch; omega) _
    have W1 : Watch f f1 :=
      ((((watch_upd f (by norm_num) (by decide) _).trans (watch_upd _ (by norm_num) (by decide) _)).trans
        (watch_upd _ (by norm_num) (by decide) _)).trans (watch_upd _ (by norm_num) (by decide) _)).trans
        (watch_upd _ (by norm_num) (by decide) _)
    have u1 : ∀ c : Int, c ≠ 1 → c ≠ 2 → c ≠ 2068 → c ≠ 2069 → c ≠ 2070 → f1 c = f c := by
      intro c a1 a2 a3 a4 a5; simp only [hf1]; rw [upd_eq _ _ a3, upd_eq _ _ a5, upd_eq _ _ a4, upd_eq _ _ a2, upd_eq _ _ a1]
    have hs1 : SymsOK b.size om f1 := by
      intro tt q h1 h2 h3 h4
      rw [u1 _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)
        (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)]
      exact hi.2.syms tt q h1 h2 h3 h4
    have e68 : f1 cK = f cK - 1 := by simp [hf1, cK]
    have e69 : f1 cACC = f cACC + t * f cWT := by simp [hf1, cACC, Function.update_apply]
    have e70 : f1 cWT = 2 * f cWT := by simp [hf1, cWT, Function.update_apply]
    have eRT : f1 cRET = f cRET := u1 _ (by unfold cRET; omega) (by unfold cRET; omega) (by unfold cRET; omega)
      (by unfold cRET; omega) (by unfold cRET; omega)
    have eM : f1 cMODE = mREAD := by rw [u1 _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)
      (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
    have hBITS : BITS f1 = BITS f - 1 := by
      unfold BITS
      rw [u1 cN (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)]
      simp only [hf1, cBY, cBI]
      simp only [Function.update_apply]
      simp only [show (1 : Int) ≠ 2068 by decide, show (1 : Int) ≠ 2069 by decide, show (1 : Int) ≠ 2070 by decide,
        show (2 : Int) ≠ 2068 by decide, show (2 : Int) ≠ 2069 by decide, show (2 : Int) ≠ 2070 by decide,
        show (1 : Int) ≠ 2 by decide, if_false, if_true]
      unfold tblNext cBY cBI at *
      split_ifs <;> simp <;> omega
    have hOUT : OUT f1 = OUT f := by
      unfold OUT
      rw [u1 cOUTMAX (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)
        (by unfold cOUTMAX; omega), u1 cM (by unfold cM; omega) (by unfold cM; omega) (by unfold cM; omega)
        (by unfold cM; omega) (by unfold cM; omega)]
    have hLOC0 : LOC f = 0 := by
      unfold LOC; rw [hm]; simp [mREAD, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN,
        mDSTX, mDSTD, mHDRD, mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]
    have hTBL : TBL f = 0 := by unfold TBL; rw [if_neg hnt]
    have hacc' : 0 ≤ f1 cACC ∧ f1 cACC < f1 cWT := by
      rw [e69, e70]; rcases ht01 with h0 | h0 <;> rw [h0] <;> constructor <;> nlinarith
    by_cases hk : f cK - 1 = 0
    · -- k reaches 0: back to rt
      rw [if_pos hk] at hS
      have hrt' : f cRET ∈ validModes := by
        simp only [readRets, validModes, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP,
          List.mem_cons, List.mem_nil_iff, or_false] at hrt ⊢; omega
      have hrt0 : f cRET ≠ mTABLE := by
        simp only [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP, mTABLE,
          List.mem_cons, List.mem_nil_iff, or_false] at hrt ⊢; omega
      have hrtR : f cRET ≠ mREAD := by
        simp only [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP, mREAD,
          List.mem_cons, List.mem_nil_iff, or_false] at hrt ⊢; omega
      have hg' : InvG b om lit (Function.update f1 0 (f cRET)) :=
        hg1.mode hrt' hrt0 (fun h => absurd h hrtR) (by rw [eM]; decide)
      have W' : Watch f (Function.update f1 0 (f cRET)) := W1.trans (watch_upd _ (by norm_num) (by decide) _)
      have eM' : Function.update f1 0 (f cRET) cMODE = f cRET := by simp [cMODE]
      have u0 : ∀ c : Int, c ≠ 0 → Function.update f1 0 (f cRET) c = f1 c := fun c hc => upd_eq _ _ hc
      have hnotin : ∀ m ∈ [mDECODE, mSYMD, mDSTD, mLSYM, mSCOPY, mREAD], f cRET ≠ m := by
        intro m hmm
        simp only [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP,
          List.mem_cons, List.mem_nil_iff, or_false] at hrt
        simp only [mDECODE, mSYMD, mDSTD, mLSYM, mSCOPY, mREAD, List.mem_cons, List.mem_nil_iff, or_false] at hmm
        omega
      have hm' : InvM b.size om (Function.update f1 0 (f cRET)) := {
        syms := SymsOK.upd hs1 (by norm_num) _
        cur := by rw [eM']; exact facts_congr W' hhl hfr
        read := fun h => by rw [eM'] at h; exact absurd h (hnotin _ (by simp))
        ret := fun _ => by
          rw [eM', u0 _ (by unfold cACC; omega)]
          refine ⟨hacc'.1, lt_of_lt_of_le hacc'.2 ?_⟩
          rw [e70]
          have : (f cK).toNat = 1 := by omega
          rw [this] at hcap; simpa [mul_comm] using hcap
        dec := fun h => by rw [eM'] at h; exact absurd h (hnotin _ (by simp))
        sym := fun h => by
          rw [eM'] at h
          rcases h with h | h | h <;> exact absurd h (hnotin _ (by simp))
        scopy := fun h => by rw [eM'] at h; exact absurd h (hnotin _ (by simp))
        ralign := fun h => by rw [eM'] at h; exact absurd h (hnotin _ (by simp))
        align := fun h => by
          rw [eM'] at h
          have h' : f cRET = mSLEN ∨ f cRET = mSNLEN := by
            rcases h with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h (hnotin _ (by simp))
          have hal := hi.2.ralign hm h'
          rw [u0 _ (by unfold cBI; omega)]
          simp only [hf1, cBI, Function.update_apply]
          simp only [show (2 : Int) ≠ 2068 by decide, show (2 : Int) ≠ 2069 by decide, show (2 : Int) ≠ 2070 by decide,
            if_false, if_true]
          simp only [cBI, cK] at hal hir hk ⊢
          unfold tblNext
          split_ifs <;> simp <;> omega }
      refine ⟨_, _, hS, hw1'.store (i := 0) (by norm_num) (by unfold L0; omega), ⟨hg', hm'⟩, Or.inl ?_⟩
      have hLt := LOC_lt hg' hm'
      have hT' : TBL (Function.update f1 0 (f cRET)) = 0 := by unfold TBL; rw [eM', if_neg hrt0]
      have hB' : BITS (Function.update f1 0 (f cRET)) = BITS f1 := by
        unfold BITS; rw [u0 _ (by unfold cN; omega), u0 _ (by unfold cBY; omega), u0 _ (by unfold cBI; omega)]
      have hO' : OUT (Function.update f1 0 (f cRET)) = OUT f1 := by
        unfold OUT; rw [u0 _ (by unfold cOUTMAX; omega), u0 _ (by unfold cM; omega)]
      unfold Φ mW at *
      rw [hT', hB', hO', hBITS, hOUT, hTBL, hLOC0]
      omega
    · -- still READ
      rw [if_neg hk] at hS
      have hg' : InvG b om lit f1 := hg1
      have hm' : InvM b.size om f1 := {
        syms := hs1
        cur := by rw [eM]; simp [facts, mREAD, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP,
          mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY]
        read := fun _ => by
          rw [eRT, e68]
          refine ⟨facts_congr W1 hhl hfr, by omega, by rw [e70]; omega, hacc'.1, hacc'.2, ?_⟩
          rw [e70]
          rw [pow_toNat_succ _ hk1] at hcap
          calc 2 * f cWT * 2 ^ (f cK - 1).toNat = f cWT * (2 * 2 ^ (f cK - 1).toNat) := by ring
            _ ≤ kcap (f cRET) := hcap
        ret := fun h => by
          rw [eM] at h; simp [readRets, mREAD, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
        dec := fun h => by rw [eM] at h; simp [mREAD, mDECODE] at h
        sym := fun h => by rw [eM] at h; simp [mREAD, mSYMD, mDSTD, mLSYM] at h
        scopy := fun h => by rw [eM] at h; simp [mREAD, mSCOPY] at h
        ralign := fun _ hr => by
          rw [eRT] at hr
          have hal := hi.2.ralign hm hr
          rw [e68]
          simp only [hf1, cBI, Function.update_apply]
          simp only [show (2 : Int) ≠ 2068 by decide, show (2 : Int) ≠ 2069 by decide, show (2 : Int) ≠ 2070 by decide,
            if_false, if_true]
          simp only [cBI, cK] at hal hir ⊢
          unfold tblNext
          split_ifs <;> simp <;> omega
        align := fun h => by rw [eM] at h; simp [mREAD, mSLEN, mSNLEN, mSCOPY] at h }
      refine ⟨_, _, hS, hw1', ⟨hg', hm'⟩, Or.inl ?_⟩
      have hLOC1 : LOC f1 = 0 := by
        unfold LOC; rw [eM]; simp [mREAD, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY,
          mSNLEN, mDSTX, mDSTD, mHDRD, mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]
      have hT1 : TBL f1 = 0 := by unfold TBL; rw [eM]; simp [mREAD, mTABLE]
      unfold Φ mW
      rw [hT1, hBITS, hOUT, hTBL, hLOC0, hLOC1]
      omega
  · -- truncated
    have hbx : f cBY = b.size := by omega
    have hstep := readbit_trunc hw (by unfold L0; omega) (f cBY) b.size rfl hn (by omega)
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2 hstep
    refine ⟨_, _, hS, (hw.store (i := 14) (by norm_num) (by unfold L0; omega)).store (i := 0) (by norm_num) (by unfold L0; omega),
      ⟨(hi.1.upd (by unfold scratch; omega) _).mode (by decide) (by decide) (fun h => by simp [mREJECT, mREAD] at h)
        (by rw [upd_eq _ _ (by unfold cMODE; omega)]; exact hnt),
       InvM.term (SymsOK.upd hi.2.syms (by norm_num) _) (Or.inr rfl)⟩, Or.inr (Or.inr (by simp [cMODE, mREJECT]))⟩

end VIRDeflate.Step
