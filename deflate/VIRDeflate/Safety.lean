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
   (tg = 1 ∧ sb = LB0 n om ∧ nn = hl ∧ hl + hd ≤ 318 ∧ 0 ≤ hd) ∨
   (tg = 2 ∧ sb = LB0 n om + hl ∧ nn = hd ∧ hl + hd ≤ 318 ∧ 0 ≤ hd ∧ sane n om f 1)) ∧
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

/-- What `facts` reads: the watched cursor cells, every cell from 2080 up to X (lengths and tables), and BUILD's parameters at
X + 5 … X + 7. Cells X … X + 4 (the decode cursor) are NOT read by `facts`. -/
def Watch (n om : Nat) (f g : Int → Int) : Prop :=
  (∀ i : Int, 2080 ≤ i → i < X0 n om → f i = g i) ∧ (∀ j : Int, 5 ≤ j → j ≤ 7 → f (X0 n om + j) = g (X0 n om + j)) ∧
    ∀ c ∈ watched, f c = g c

theorem sane_congr {n om : Nat} {f g : Int → Int} (h : ∀ i : Int, 2080 ≤ i → i < X0 n om → f i = g i) {t : Int}
    (ht : 0 ≤ t) (ht2 : t ≤ 2) (hs : sane n om f t) : sane n om g t := by
  intro l h1 h2
  have a := h (tbase n om t + l) (by unfold tbase LB0; omega) (by unfold tbase LB0 X0; omega)
  have b := h (tbase n om t + 32 + l) (by unfold tbase LB0; omega) (by unfold tbase LB0 X0; omega)
  rw [← a, ← b]; exact hs l h1 h2

theorem cnt_congr {f g : Int → Int} {X : Int} (h : ∀ i : Int, 2080 ≤ i → i < X → f i = g i) {sb l : Int}
    (hsb : 2080 ≤ sb) : ∀ k : Nat, sb + k ≤ X → cnt f sb l k = cnt g sb l k
  | 0, _ => rfl
  | k + 1, hk => by simp only [cnt, cnt_congr h hsb k (by omega), h (sb + k) (by omega) (by omega)]

theorem offOf_congr {f g : Int → Int} {X : Int} (h : ∀ i : Int, 2080 ≤ i → i < X → f i = g i) {tbb : Int}
    (htb : 2080 ≤ tbb) : ∀ l : Nat, tbb + l ≤ X → offOf f tbb l = offOf g tbb l
  | 0, _ => rfl
  | l + 1, hl => by simp only [offOf, offOf_congr h htb l (by omega), h (tbb + l) (by omega) (by omega)]

theorem buildInv_congr {n om : Nat} {f g : Int → Int} (hw : Watch n om f g) (hhl : 0 ≤ f cHLIT) (hb : buildInv n om f) :
    buildInv n om g := by
  obtain ⟨hi, hx, hc⟩ := hw
  have e5 := hx 5 (by norm_num) (by norm_num)
  have e6 := hx 6 (by norm_num) (by norm_num)
  have e7 := hx 7 (by norm_num) (by norm_num)
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
  have htbX : f (X0 n om + 7) + 64 ≤ X0 n om := by rw [htb]; unfold tbase LB0 X0; omega
  have hsb : (2080 : Int) ≤ f (X0 n om + 5) := by
    rcases htg with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> rw [h] <;> unfold LB0 <;> omega
  have hsbX : f (X0 n om + 5) + (f (X0 n om + 6)).toNat ≤ X0 n om := by
    rcases htg with ⟨_, h, h', _⟩ | ⟨_, h, h', _, _⟩ | ⟨_, h, h', _, _⟩ <;> rw [h, h'] <;> unfold LB0 X0 <;> omega
  have hcnt : ∀ (l : Int) (k : Nat), k ≤ (f (X0 n om + 6)).toNat →
      cnt f (f (X0 n om + 5)) l k = cnt g (f (X0 n om + 5)) l k :=
    fun l k hk => cnt_congr hi (l := l) hsb k (by omega)
  have hoff : ∀ l : Nat, l ≤ 16 → offOf f (f (X0 n om + 7)) l = offOf g (f (X0 n om + 7)) l :=
    fun l hl => offOf_congr hi htb2 l (by omega)
  have hi' : ∀ k : Int, 0 ≤ k → k < 64 → f (f (X0 n om + 7) + k) = g (f (X0 n om + 7) + k) :=
    fun k a b' => hi _ (by omega) (by omega)
  refine ⟨ht0, ht2, htb, ?_, ?_, ?_, ?_, ?_, hph⟩
  · rcases htg with h | h | ⟨a, b', c, d, e⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨e1, e2⟩ := e
      exact Or.inr (Or.inr ⟨a, b', c, d, e1, sane_congr hi (by norm_num) (by norm_num) e2⟩)
  · intro hp
    obtain ⟨a, b', c⟩ := h0 hp
    exact ⟨a, b', fun l l0 lj => by rw [← hi' l l0 (by omega)]; exact c l l0 lj⟩
  · intro hp
    obtain ⟨a, b', c, d⟩ := h1 hp
    refine ⟨a, b', by rw [← hi _ htb2 (by omega)]; exact c, fun l l1 l15 => ?_⟩
    rw [← hi' l (by omega) (by omega), ← hcnt l _ (by omega)]; exact d l l1 l15
  · intro hp2 hp3
    obtain ⟨a, b', c, d, e, g'⟩ := h23 hp2 hp3
    refine ⟨a, b', ?_, by rw [← hi' 32 (by norm_num) (by norm_num)]; exact d, fun l l1 l15 => ?_, fun l l1 lj => ?_⟩
    · have := hi' 0 (le_refl _) (by norm_num); simp only [add_zero] at this; rw [← this]; exact c
    · rw [← hi' l (by omega) (by omega), ← hcnt l _ (le_refl _)]; exact e l l1 l15
    · have hl16 : l < 16 := by split_ifs at lj <;> omega
      rw [← hi (f (X0 n om + 7) + 32 + l) (by omega) (by omega), ← hi (f (X0 n om + 7) + 48 + l) (by omega) (by omega),
        ← hoff _ (by omega)]
      exact g' l l1 lj
  · intro hp
    obtain ⟨a, b', c, d⟩ := h4 hp
    refine ⟨a, b', sane_congr hi ht0 ht2 c, fun l l1 l15 => ?_⟩
    rw [← hi (f (X0 n om + 7) + 48 + l) (by omega) (by omega), ← hcnt l _ (le_refl _), ← hcnt l _ (by omega)]
    exact d l l1 l15

theorem ite_imp {c : Prop} [Decidable c] {a b a' b' : Prop} (h1 : a → a') (h2 : b → b') :
    (if c then a else b) → (if c then a' else b') := by
  split_ifs <;> assumption

theorem facts_congr {n om : Nat} {f g : Int → Int} (hw : Watch n om f g) (hhl : 0 ≤ f cHLIT) {md : Int}
    (hf : facts n om md f) : facts n om md g := by
  have hb := fun h => buildInv_congr (n := n) (om := om) hw hhl h
  obtain ⟨hi, _, hc⟩ := hw
  have s0 := sane_congr (n := n) (om := om) hi (t := 0) (le_refl _) (by norm_num)
  have s1 := sane_congr (n := n) (om := om) hi (t := 1) (by norm_num) (by norm_num)
  have s2 := sane_congr (n := n) (om := om) hi (t := 2) (by norm_num) (by norm_num)
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

theorem watch_reqF {n om : Nat} (f : Int → Int) (k rt : Int) : Watch n om f (reqF f k rt) := by
  refine ⟨fun i hi _ => (reqF_eq f k rt i (by omega)).symm,
    fun j _ _ => (reqF_eq f k rt _ (by unfold X0; omega)).symm, fun c hc => ?_⟩
  simp only [watched, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rw [reqF_eq f k rt c (by omega)]

theorem watch_upd {n om : Nat} (f : Int → Int) {i : Int} (hi : i < 2080) (hw : i ∉ watched) (v : Int) :
    Watch n om f (Function.update f i v) := by
  refine ⟨fun j hj _ => (upd_eq f v (by omega)).symm, fun j _ _ => (upd_eq f v (by unfold X0; omega)).symm, fun c hc => ?_⟩
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
  have W : Watch n om f (Function.update f i v) := watch_upd f hi hw v
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
    rcases d with ⟨d1, _⟩ | ⟨d1, _⟩ | ⟨d1, _⟩ <;> rw [d1] at e ⊢ <;> exact sane_congr W.1 (by norm_num) (by norm_num) e
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

theorem Watch.trans {n om : Nat} {f g h : Int → Int} (a : Watch n om f g) (b : Watch n om g h) : Watch n om f h :=
  ⟨fun i hi hX => (a.1 i hi hX).trans (b.1 i hi hX), fun j h1 h2 => (a.2.1 j h1 h2).trans (b.2.1 j h1 h2),
    fun c hc => (a.2.2 c hc).trans (b.2.2 c hc)⟩

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
    have W1 : Watch b.size om f f1 :=
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
      have W' : Watch b.size om f (Function.update f1 0 (f cRET)) := W1.trans (watch_upd _ (by norm_num) (by decide) _)
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

/-! ## Helpers: the header cells, SHDR's alignment, a plain mode switch -/

theorem InvG.hdr {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {i : Int}
    (hi : i = 7 ∨ i = 8 ∨ i = 9) (v : Int)
    (hr : 0 ≤ Function.update f i v cHLIT ∧ Function.update f i v cHLIT ≤ 288 ∧ 0 ≤ Function.update f i v cHDIST ∧
      Function.update f i v cHDIST ≤ 32 ∧ 0 ≤ Function.update f i v cHCLEN ∧ Function.update f i v cHCLEN ≤ 19) :
    InvG b om lit (Function.update f i v) := by
  have u : ∀ c : Int, c ≠ i → Function.update f i v c = f c := fun c hc => upd_eq f v hc
  exact {
  n_eq := by rw [u _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun j h1 h2 => by rw [u _ (by omega)]; exact h.input j h1 h2
  ro := fun j h1 h2 => by rw [u _ (by unfold X0 at h1; omega)]; exact h.ro j h1 h2
  lens := fun j h1 h2 => by rw [u _ (by omega)]; exact h.lens j h1 h2
  tb_rng := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)]; exact h.tb_rng hm
  bits := fun c h1 h2 h3 => by
    rw [u _ (by unfold cMODE; omega), u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)] at h3
    rw [u _ (by unfold BT; omega)]; exact h.bits c h1 h2 h3
  by_rng := by rw [u _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [u _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [u _ (by unfold cBY; omega), u _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [u _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [u _ (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm; rw [u _ (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := hr }

/-- SHDR's alignment: by → by (bi = 0) or by + 1 (bi ≠ 0, so by < n), bi → 0. -/
theorem InvG.align {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) :
    InvG b om lit (Function.update (Function.update f 1 (if f cBI = 0 then f cBY else f cBY + 1)) 2 0) := by
  have u : ∀ c : Int, c ≠ 1 → c ≠ 2 →
      Function.update (Function.update f 1 (if f cBI = 0 then f cBY else f cBY + 1)) 2 0 c = f c :=
    fun c h1 h2 => by rw [upd_eq _ _ h2, upd_eq _ _ h1]
  have e1 : Function.update (Function.update f 1 (if f cBI = 0 then f cBY else f cBY + 1)) 2 0 cBY =
      (if f cBI = 0 then f cBY else f cBY + 1) := by simp [cBY]
  have e2 : Function.update (Function.update f 1 (if f cBI = 0 then f cBY else f cBY + 1)) 2 0 cBI = 0 := by simp [cBI]
  have hbr := h.by_rng
  have hir := h.bi_rng
  have hbe := h.by_end
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
  by_rng := by
    rw [e1]; split_ifs with hz
    · exact hbr
    · by_cases he : f cBY = b.size
      · exact absurd (hbe he) hz
      · omega
  bi_rng := by rw [e2]; omega
  by_end := fun _ => e2
  m_rng := by rw [u _ (by unfold cM; omega) (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cRET; omega) (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega) (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega) (by unfold cHDIST; omega),
      u _ (by unfold cHCLEN; omega) (by unfold cHCLEN; omega)]; exact h.hdr_rng }

/-- A plain mode switch: into a mode with no READ, DECODE, symbol, SCOPY or alignment obligation. -/
theorem InvM.mode {n om : Nat} {g : Int → Int} (hs : SymsOK n om g) {v : Int}
    (hv : v ∉ [mREAD, mDECODE, mSYMD, mDSTD, mLSYM, mSCOPY, mSLEN, mSNLEN]) (hvr : v ∉ readRets)
    (hf : facts n om v (Function.update g 0 v)) : InvM n om (Function.update g 0 v) := by
  have hm : Function.update g 0 v cMODE = v := by simp [cMODE]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  exact {
  syms := SymsOK.upd hs (by norm_num) _
  cur := by rw [hm]; exact hf
  read := fun h => by rw [hm] at h; exact absurd h h1
  ret := fun h => by rw [hm] at h; exact absurd h hvr
  dec := fun h => by rw [hm] at h; exact absurd h h2
  sym := fun h => by rw [hm] at h; rcases h with h | h | h <;> contradiction
  scopy := fun h => by rw [hm] at h; exact absurd h h6
  ralign := fun h => by rw [hm] at h; exact absurd h h1
  align := fun h => by rw [hm] at h; rcases h with h | h | h <;> contradiction }

/-! ## DH2, DH3, SHDR, HDRD -/

theorem safeI_dh2 {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDH2) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mDH2, dh2N) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDH2, dh2N) hmem (by decide)
  have hacc := hi.2.ret (by rw [hm]; decide)
  rw [hm] at hacc; simp only [kcap, mDH2, mHDRB, mHDRD, mSLEN, mSNLEN] at hacc; norm_num at hacc
  have hr := hi.1.hdr_rng
  have hg1 := hi.1.hdr (i := 7) (by norm_num) (f cACC + 257) (by simp [cHLIT, cHDIST, cHCLEN] at hr ⊢; omega)
  refine ⟨_, _, stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (dh2_step hw hL (f cACC) rfl),
    (hw.store (i := 7) (by norm_num) (by omega)).req (by omega) 5 21,
    ⟨hg1.req (by rw [upd_eq _ _ (by unfold cMODE; omega), hm]; decide) 5 (by decide),
     InvM.req (SymsOK.upd hi.2.syms (by norm_num) _) (by simp [cHLIT] at hr ⊢; omega)
       (by simp [facts, mDH3, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX,
         mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mDH3, mDH2, mHDRB, mHDRD, mSLEN, mSNLEN])
       (fun h => by simp [mDH3, mSLEN, mSNLEN] at h)⟩, Or.inl ?_⟩
  simp only [reqF]
  simp only [cMODE, mDH2] at hm
  phisimp
  simp [hm]

theorem safeI_dh3 {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDH3) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mDH3, dh3N) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDH3, dh3N) hmem (by decide)
  have hacc := hi.2.ret (by rw [hm]; decide)
  rw [hm] at hacc; simp only [kcap, mDH3, mDH2, mHDRB, mHDRD, mSLEN, mSNLEN] at hacc; norm_num at hacc
  have hr := hi.1.hdr_rng
  have hg1 := hi.1.hdr (i := 8) (by norm_num) (f cACC + 1) (by simp [cHLIT, cHDIST, cHCLEN] at hr ⊢; omega)
  refine ⟨_, _, stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (dh3_step hw hL (f cACC) rfl),
    (hw.store (i := 8) (by norm_num) (by omega)).req (by omega) 4 22,
    ⟨hg1.req (by rw [upd_eq _ _ (by unfold cMODE; omega), hm]; decide) 4 (by decide),
     InvM.req (SymsOK.upd hi.2.syms (by norm_num) _) (by simp [cHLIT] at hr ⊢; omega)
       (by simp [facts, mDH4, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX,
         mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mDH4, mDH3, mDH2, mHDRB, mHDRD, mSLEN, mSNLEN])
       (fun h => by simp [mDH4, mSLEN, mSNLEN] at h)⟩, Or.inl ?_⟩
  simp only [reqF]
  simp only [cMODE, mDH3] at hm
  phisimp
  simp [hm]

theorem safeI_shdr {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSHDR) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mSHDR, shdrN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSHDR, shdrN) hmem (by decide)
  have hr := hi.1.hdr_rng
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hbe := hi.1.by_end
  set g := Function.update (Function.update f 1 (if f cBI = 0 then f cBY else f cBY + 1)) 2 0 with hg
  have hgBI : g cBI = 0 := by simp [hg, cBI]
  refine ⟨_, _, stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (shdr_step hw hL (f cBY) (f cBI) rfl rfl),
    ((hw.store (i := 1) (by norm_num) (by omega)).store (i := 2) (by norm_num) (by omega)).req (by omega) 16 8,
    ⟨hi.1.align.req (by rw [upd_eq _ _ (by unfold cMODE; omega), upd_eq _ _ (by unfold cMODE; omega), hm]; decide) 16
      (by decide),
     InvM.req (SymsOK.upd (SymsOK.upd hi.2.syms (by norm_num) _) (by norm_num) _)
       (by rw [upd_eq _ _ (by unfold cHLIT; omega), upd_eq _ _ (by unfold cHLIT; omega)]; exact hr.1)
       (by simp [facts, mSLEN, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX,
         mDSTD, mDSTX, mCOPY]) (by norm_num) (by simp [kcap, mSLEN, mHDRB, mHDRD])
       (fun _ => by simp [cBI])⟩, Or.inl ?_⟩
  have u : ∀ c : Int, c ≠ 1 → c ≠ 2 → (c < 2068 ∧ c ≠ 0) ∨ 2071 < c → reqF g 16 8 c = f c := by
    intro c h1 h2 h3; rw [reqF_eq _ _ _ _ h3, hg, upd_eq _ _ h2, upd_eq _ _ h1]
  have hT : TBL (reqF g 16 8) = 0 := by unfold TBL; simp [reqF, cMODE, mTABLE]
  have hTf : TBL f = 0 := by unfold TBL; rw [hm]; simp [mSHDR, mTABLE]
  have hO : OUT (reqF g 16 8) = OUT f := by
    unfold OUT; rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega),
      u _ (by unfold cM; omega) (by unfold cM; omega) (by unfold cM; omega)]
  have hB : BITS (reqF g 16 8) ≤ BITS f := by
    unfold BITS
    rw [u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega),
      reqF_eq _ _ _ _ (by unfold cBY; omega), reqF_eq _ _ _ _ (by unfold cBI; omega), hgBI]
    simp only [hg, cBY, Function.update_apply]
    simp only [show (1 : Int) ≠ 2 by decide, if_false, if_true]
    simp only [cBI, cBY] at hir hbr ⊢
    split_ifs <;> omega
  have hL1 : LOC f = 1 := by unfold LOC; rw [hm]; simp [mSHDR, mHDR, mHDRB]
  have hL0 : LOC (reqF g 16 8) = 0 := by
    unfold LOC; rw [show reqF g 16 8 cMODE = 2 by simp [reqF, cMODE]]
    simp [mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD, mHDRD, mFIXLENS,
      mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]
  rw [← hg]; unfold Φ mW; rw [hT, hTf, hO, hL1, hL0]; omega

theorem Φ_lt_of {f f' : Int → Int} (hT : TBL f' = TBL f) (hB : BITS f' = BITS f) (hO : OUT f' = OUT f)
    (hL : LOC f' < LOC f) : Φ f' < Φ f := by unfold Φ; rw [hT, hB, hO]; omega

/-- A mode switch (cell 0) after writes to cells that neither BITS nor OUT reads keeps TBL (both non-TABLE), BITS, OUT. -/
theorem TBO_eq {f f' : Int → Int} (hnt : f cMODE ≠ mTABLE) (hnt' : f' cMODE ≠ mTABLE)
    (e : ∀ c : Int, c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 15 ∨ c = 16 → f' c = f c) :
    TBL f' = TBL f ∧ BITS f' = BITS f ∧ OUT f' = OUT f := by
  refine ⟨by unfold TBL; rw [if_neg hnt, if_neg hnt'], ?_, ?_⟩
  · unfold BITS; rw [e cN (by unfold cN; omega), e cBY (by unfold cBY; omega), e cBI (by unfold cBI; omega)]
  · unfold OUT; rw [e cOUTMAX (by unfold cOUTMAX; omega), e cM (by unfold cM; omega)]

theorem safeI_hdrd {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mHDRD) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mHDRD, hdrdN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mHDRD, hdrdN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (hdrd_step hw hL (f cACC) rfl)
  have hL1 : LOC f = 1 + locFIX 0 := by unfold LOC; rw [hm]; simp [mHDRD, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM,
    mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD]
  have hlf : 0 < locFIX 0 := by unfold locFIX bfull; norm_num
  unfold hdrdH at hS
  by_cases a0 : f cACC = 0
  · rw [if_pos a0] at hS
    refine ⟨_, _, hS, hw.store (i := 0) (by norm_num) (by omega),
      ⟨hi.1.mode (by decide) (by decide) (fun h => by simp [mREAD] at h) hnt,
       InvM.mode hi.2.syms (by decide) (by decide) (by simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS,
         mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY])⟩, Or.inl ?_⟩
    obtain ⟨t1, t2, t3⟩ := TBO_eq (f' := Function.update f 0 5) hnt (by simp [cMODE, mTABLE])
      (fun c hc => upd_eq _ _ (by omega))
    refine Φ_lt_of t1 t2 t3 ?_
    rw [hL1]; unfold LOC; simp [cMODE, mSHDR, mHDR, mHDRB]; omega
  by_cases a1 : f cACC = 1
  · rw [if_neg a0, if_pos a1] at hS
    refine ⟨_, _, hS, (hw.store (i := 10) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega),
      ⟨(hi.1.upd (by unfold scratch; omega) _).mode (by decide) (by decide) (fun h => by simp [mREAD] at h)
        (by rw [upd_eq _ _ (by unfold cMODE; omega)]; exact hnt),
       InvM.mode (SymsOK.upd hi.2.syms (by norm_num) _) (by decide) (by decide)
         (by simp [facts, mFIXLENS, mSNLEN, mSCOPY, cFILL])⟩, Or.inl ?_⟩
    obtain ⟨t1, t2, t3⟩ := TBO_eq (f' := Function.update (Function.update f 10 0) 0 6) hnt (by simp [cMODE, mTABLE])
      (fun c hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
    refine Φ_lt_of t1 t2 t3 ?_
    rw [hL1]; unfold LOC
    simp [cMODE, cFILL, mFIXLENS, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN,
      mDSTX, mDSTD, mHDRD]
  by_cases a2 : f cACC = 2
  · rw [if_neg a0, if_neg a1, if_pos a2] at hS
    refine ⟨_, _, hS, hw.store (i := 0) (by norm_num) (by omega),
      ⟨hi.1.mode (by decide) (by decide) (fun h => by simp [mREAD] at h) hnt,
       InvM.mode hi.2.syms (by decide) (by decide) (by simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS,
         mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY])⟩, Or.inl ?_⟩
    obtain ⟨t1, t2, t3⟩ := TBO_eq (f' := Function.update f 0 7) hnt (by simp [cMODE, mTABLE])
      (fun c hc => upd_eq _ _ (by omega))
    refine Φ_lt_of t1 t2 t3 ?_
    rw [hL1]; unfold LOC; simp [cMODE, mDHDR, mHDR, mHDRB, mSHDR, mSLEN]; omega
  · rw [if_neg a0, if_neg a1, if_neg a2] at hS
    exact ⟨_, _, hS, (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega),
      ⟨(hi.1.upd (by unfold scratch; omega) _).mode (by decide) (by decide) (fun h => by simp [mREJECT, mREAD] at h)
        (by rw [upd_eq _ _ (by unfold cMODE; omega)]; exact hnt),
       InvM.term (SymsOK.upd hi.2.syms (by norm_num) _) (Or.inr rfl)⟩, Or.inr (Or.inr (by simp [cMODE, mREJECT]))⟩

/-! ## The stored path: SNLEN, SCOPY -/

/-- A write into the output area [2080 + n, 2080 + n + OUTMAX) keeps InvG. -/
theorem InvG.out {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {i : Int}
    (h0 : 2080 + b.size ≤ i) (h1 : i < 2080 + b.size + om) (v : Int) : InvG b om lit (Function.update f i v) := by
  have u : ∀ c : Int, c ≠ i → Function.update f i v c = f c := fun c hc => upd_eq f v hc
  exact {
  n_eq := by rw [u _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun j a b' => by rw [u _ (by omega)]; exact h.input j a b'
  ro := fun j a b' => by rw [u _ (by unfold X0 at a; omega)]; exact h.ro j a b'
  lens := fun j a b' => by rw [u _ (by omega)]; exact h.lens j a b'
  tb_rng := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)]; exact h.tb_rng hm
  bits := fun c a b' h3 => by
    rw [u _ (by unfold cMODE; omega), u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)] at h3
    rw [u _ (by unfold BT; omega)]; exact h.bits c a b' h3
  by_rng := by rw [u _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [u _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [u _ (by unfold cBY; omega), u _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [u _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [u _ (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm; rw [u _ (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega), u _ (by unfold cHCLEN; omega)]; exact h.hdr_rng }

/-- New values for the byte cursor (cell 1) and the output length (cell 3), in range. -/
theorem InvG.c13 {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {v1 v3 : Int}
    (h1 : 0 ≤ v1 ∧ v1 ≤ b.size) (h3 : 0 ≤ v3 ∧ v3 ≤ om) (he : v1 = b.size → f cBI = 0) :
    InvG b om lit (Function.update (Function.update f 1 v1) 3 v3) := by
  have u : ∀ c : Int, c ≠ 1 → c ≠ 3 → Function.update (Function.update f 1 v1) 3 v3 c = f c :=
    fun c a b' => by rw [upd_eq _ _ b', upd_eq _ _ a]
  have e1 : Function.update (Function.update f 1 v1) 3 v3 cBY = v1 := by simp [cBY]
  have e3 : Function.update (Function.update f 1 v1) 3 v3 cM = v3 := by simp [cM]
  exact {
  n_eq := by rw [u _ (by unfold cN; omega) (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega) (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega) (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun j a b' => by rw [u _ (by omega) (by omega)]; exact h.input j a b'
  ro := fun j a b' => by rw [u _ (by unfold X0 at a; omega) (by unfold X0 at a; omega)]; exact h.ro j a b'
  lens := fun j a b' => by rw [u _ (by omega) (by omega)]; exact h.lens j a b'
  tb_rng := fun hm => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cTB; omega) (by unfold cTB; omega), u _ (by unfold cTI; omega) (by unfold cTI; omega)]
    exact h.tb_rng hm
  bits := fun c a b' h3' => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega), u _ (by unfold cTB; omega) (by unfold cTB; omega),
      u _ (by unfold cTI; omega) (by unfold cTI; omega)] at h3'
    rw [u _ (by unfold BT; omega) (by unfold BT; omega)]; exact h.bits c a b' h3'
  by_rng := by rw [e1]; exact h1
  bi_rng := by rw [u _ (by unfold cBI; omega) (by unfold cBI; omega)]; exact h.bi_rng
  by_end := fun hb => by rw [e1] at hb; rw [u _ (by unfold cBI; omega) (by unfold cBI; omega)]; exact he hb
  m_rng := by rw [e3]; exact h3
  mode_ok := by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cRET; omega) (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega) (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega) (by unfold cHDIST; omega),
      u _ (by unfold cHCLEN; omega) (by unfold cHCLEN; omega)]; exact h.hdr_rng }

theorem safeI_snlen {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSNLEN) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mSNLEN, snlenN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSNLEN, snlenN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (snlen_step hw hL (f cACC) (f cPEND) (f cBY) (f cN) (f cM) (f cOUTMAX) rfl rfl rfl rfl rfl rfl)
  have hc := hi.2.cur
  rw [hm] at hc; simp only [facts, mSNLEN, if_true] at hc
  have hbi0 := hi.2.align (Or.inr (Or.inl hm))
  have rej : ∀ r : Int, ∃ σ' f', stepS p σ = some ⟨(σ.H.insert (p + 14) r).insert (p + 0) 99, σ.R⟩ →
      (stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
        (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT)) := fun r =>
    ⟨_, _, fun hS' => ⟨hS', (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega),
      ⟨(hi.1.upd (by unfold scratch; omega) _).mode (by decide) (by decide) (fun h => by simp [mREJECT, mREAD] at h)
        (by rw [upd_eq _ _ (by unfold cMODE; omega)]; exact hnt),
       InvM.term (SymsOK.upd hi.2.syms (by norm_num) _) (Or.inr rfl)⟩, Or.inr (Or.inr (by simp [cMODE, mREJECT]))⟩⟩
  unfold snlenH at hS
  by_cases h1 : f cACC + f cPEND = 65535
  · rw [if_pos h1] at hS
    by_cases h2 : f cN < f cBY + f cPEND
    · rw [if_pos h2] at hS; obtain ⟨σ', f', k⟩ := rej 1; exact ⟨σ', f', k hS⟩
    · rw [if_neg h2] at hS
      by_cases h3 : f cOUTMAX < f cM + f cPEND
      · rw [if_pos h3] at hS; obtain ⟨σ', f', k⟩ := rej 4; exact ⟨σ', f', k hS⟩
      · rw [if_neg h3] at hS
        have hm' : Function.update f 0 10 cMODE = 10 := by simp [cMODE]
        have u : ∀ c : Int, c ≠ 0 → Function.update f 0 10 c = f c := fun c hc => upd_eq _ _ hc
        refine ⟨_, _, hS, hw.store (i := 0) (by norm_num) (by omega),
          ⟨hi.1.mode (by decide) (by decide) (fun h => by simp [mREAD] at h) hnt, {
            syms := SymsOK.upd hi.2.syms (by norm_num) _
            cur := by
              rw [hm']; unfold facts
              rw [u cPEND (by unfold cPEND; omega), u cM (by unfold cM; omega), u cOUTMAX (by unfold cOUTMAX; omega)]
              simp [mSNLEN, mSCOPY]; omega
            read := fun h => by rw [hm'] at h; simp [mREAD] at h
            ret := fun h => by
              rw [hm'] at h; simp [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
            dec := fun h => by rw [hm'] at h; simp [mDECODE] at h
            sym := fun h => by rw [hm'] at h; simp [mSYMD, mDSTD, mLSYM] at h
            scopy := fun _ => by
              rw [u _ (by unfold cBY; omega), u _ (by unfold cPEND; omega), u _ (by unfold cN; omega)]; omega
            ralign := fun h => by rw [hm'] at h; simp [mREAD] at h
            align := fun _ => by rw [u _ (by unfold cBI; omega)]; exact hbi0 }⟩, Or.inl ?_⟩
        obtain ⟨t1, t2, t3⟩ := TBO_eq (f' := Function.update f 0 10) hnt (by simp [cMODE, mTABLE])
          (fun c hc => upd_eq _ _ (by omega))
        refine Φ_lt_of t1 t2 t3 ?_
        unfold LOC; rw [hm, hm']; simp [mSNLEN, mSCOPY, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mCOPY,
          mDSTX]
  · rw [if_neg h1] at hS; obtain ⟨σ', f', k⟩ := rej 3; exact ⟨σ', f', k hS⟩

theorem safeI_scopy {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSCOPY) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mSCOPY, scopyN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSCOPY, scopyN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hc := hi.2.cur
  rw [hm] at hc; simp only [facts, show mSCOPY = (10 : Int) by rfl, show ¬ ((10 : Int) = mSNLEN) by decide, if_false,
    if_true] at hc
  have hsc := hi.2.scopy hm
  have hbi0 := hi.2.align (Or.inr (Or.inr hm))
  have hn := hi.1.n_eq
  have hom := hi.1.om_eq
  have hbr := hi.1.by_rng
  have hmr := hi.1.m_rng
  by_cases hk : f cPEND = 0
  · have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (scopy_end hw hL (f cBF) hk rfl)
    by_cases hbf : f cBF = 1
    · rw [if_pos hbf] at hS
      exact ⟨_, _, hS, hw.store (i := 0) (by norm_num) (by omega),
        ⟨hi.1.mode (by decide) (by decide) (fun h => by simp [mDONE, mREAD] at h) hnt,
         InvM.term hi.2.syms (Or.inl rfl)⟩, Or.inr (Or.inl (by simp [cMODE, mDONE]))⟩
    · rw [if_neg hbf] at hS
      refine ⟨_, _, hS, hw.store (i := 0) (by norm_num) (by omega),
        ⟨hi.1.mode (by decide) (by decide) (fun h => by simp [mREAD] at h) hnt,
         InvM.mode hi.2.syms (by decide) (by decide) (by simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS,
           mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY])⟩, Or.inl ?_⟩
      obtain ⟨t1, t2, t3⟩ := TBO_eq (f' := Function.update f 0 1) hnt (by simp [cMODE, mTABLE])
        (fun c hc => upd_eq _ _ (by omega))
      refine Φ_lt_of t1 t2 t3 ?_
      unfold LOC; rw [hm]; simp [cMODE, mSCOPY, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD]
  · have hk1 : 1 ≤ f cPEND := by omega
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (scopy_byte hw (f cBY).toNat b.size (f cM).toNat om (f cPEND) (f (IN + ((f cBY).toNat : Int))) (by unfold L0; omega)
        rfl hk (by omega) hn (by omega) rfl (by omega) (by omega))
    push_cast at hS
    simp only [show ((f cBY).toNat : Int) = f cBY by omega, show ((f cM).toNat : Int) = f cM by omega] at hS
    set g := Function.update f (2080 + b.size + f cM) (f (IN + f cBY)) with hg
    have hgi : ∀ c : Int, c < 2080 → g c = f c := fun c hc => by rw [hg, upd_eq _ _ (by omega)]
    set f' := Function.update (Function.update (Function.update g 1 (f cBY + 1)) 3 (f cM + 1)) 5 (f cPEND - 1) with hf'
    have u : ∀ c : Int, c < 2080 → c ≠ 1 → c ≠ 3 → c ≠ 5 → f' c = f c := by
      intro c a1 a2 a3 a4; rw [hf', upd_eq _ _ a4, upd_eq _ _ a3, upd_eq _ _ a2, hgi c a1]
    have e1 : f' cBY = f cBY + 1 := by simp [hf', cBY]
    have e3 : f' cM = f cM + 1 := by simp [hf', cM]
    have e5 : f' cPEND = f cPEND - 1 := by simp [hf', cPEND]
    have eM : f' cMODE = mSCOPY := by
      rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
    have eBI : f' cBI = 0 := by
      rw [u _ (by unfold cBI; omega) (by unfold cBI; omega) (by unfold cBI; omega) (by unfold cBI; omega)]; exact hbi0
    have eN : f' cN = f cN := u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)
    have eOM : f' cOUTMAX = f cOUTMAX := u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)
      (by unfold cOUTMAX; omega)
    have hgG : InvG b om lit g := hi.1.out (by omega) (by omega) _
    have hgBI : g cBI = 0 := by rw [hgi _ (by unfold cBI; omega)]; exact hbi0
    refine ⟨_, f', hS, (((hw.store (i := 2080 + b.size + f cM) (by omega) (by unfold L0; omega)).store (i := 1) (by norm_num)
      (by unfold L0; omega)).store (i := 3) (by norm_num) (by unfold L0; omega)).store (i := 5) (by norm_num)
      (by unfold L0; omega),
      ⟨(hgG.c13 (v1 := f cBY + 1) (v3 := f cM + 1) (by omega) (by omega) (fun _ => hgBI)).upd (by unfold scratch; omega) _, {
        syms := fun t q h1 h2 h3 h4 => by
          rw [hf', upd_eq _ _ (by unfold tbase LB0; omega), upd_eq _ _ (by unfold tbase LB0; omega),
            upd_eq _ _ (by unfold tbase LB0; omega), hg, upd_eq _ _ (by unfold tbase LB0; omega)]
          exact hi.2.syms t q h1 h2 h3 h4
        cur := by
          rw [eM]; simp only [facts, show mSCOPY = (10 : Int) by rfl, show ¬ ((10 : Int) = mSNLEN) by decide, if_false,
            if_true]
          rw [e5, e3, eOM]; omega
        read := fun h => by rw [eM] at h; simp [mSCOPY, mREAD] at h
        ret := fun h => by
          rw [eM] at h; simp [readRets, mSCOPY, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
        dec := fun h => by rw [eM] at h; simp [mSCOPY, mDECODE] at h
        sym := fun h => by rw [eM] at h; simp [mSCOPY, mSYMD, mDSTD, mLSYM] at h
        scopy := fun _ => by rw [e1, e5, eN]; omega
        ralign := fun h => by rw [eM] at h; simp [mSCOPY, mREAD] at h
        align := fun _ => eBI }⟩, Or.inl ?_⟩
    have hT : TBL f' = TBL f := by unfold TBL; rw [eM, hm]; simp [mSCOPY, mTABLE]
    have hLc : LOC f' = LOC f := by
      unfold LOC; rw [eM, hm]; simp [mSCOPY, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mCOPY]
    unfold Φ mW BITS OUT
    rw [hT, hLc, e1, eBI, eN, eOM, e3, hbi0]
    omega

/-! ## TABLE -/

theorem bitAt_01 (v i : Nat) (hv : v < 256) (hi : i < 8) : bitAt v i = 0 ∨ bitAt v i = 1 := by
  rw [bitAt_eq v i hv hi, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (v >>> i) with h | h <;> simp [h]

theorem safeI_table {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mTABLE) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2068 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨tb0, tb256, ti0, ti7⟩ := hi.1.tb_rng hm
  have hS := stepS_table hw hL (f cTB).toNat (f cTI).toNat hm (by omega) (by omega) (by omega) (by omega)
  simp only [show ((f cTB).toNat : Int) = f cTB by omega, show ((f cTI).toNat : Int) = f cTI by omega] at hS
  have hbit := bitAt_01 (f cTB).toNat (f cTI).toNat (by omega) (by omega)
  simp only [show ((f cTB).toNat : Int) = f cTB by omega] at hbit
  set c0 := 8 * f cTB + f cTI with hc0
  set nb := tblNext (f cTB) (f cTI) with hnb
  have hnb1 : 8 * nb.1 + nb.2 = c0 + 1 := by simp only [hnb, hc0, tblNext]; split_ifs <;> simp <;> omega
  have hnbr : 0 ≤ nb.2 ∧ nb.2 ≤ 7 ∧ 0 ≤ nb.1 ∧ nb.1 ≤ 256 := by
    simp only [hnb, tblNext]; split_ifs <;> simp <;> omega
  set g := Function.update (Function.update (Function.update f (20 + c0) (bitAt (f cTB) (f cTI).toNat)) 18 nb.1) 19 nb.2
    with hg
  have hgw : World ⟨tblH σ.H p (f cTB) (f cTI), σ.R⟩ p (L0 b.size om) g := by
    unfold tblH
    exact ((hw.store (i := 20 + c0) (by omega) (by unfold L0; omega)).store (i := 18) (by norm_num)
      (by unfold L0; omega)).store (i := 19) (by norm_num) (by unfold L0; omega)
  have u : ∀ c : Int, c ≠ 20 + c0 → c ≠ 18 → c ≠ 19 → g c = f c := fun c a1 a2 a3 => by
    rw [hg, upd_eq _ _ a3, upd_eq _ _ a2, upd_eq _ _ a1]
  have eTB : g cTB = nb.1 := by simp [hg, cTB]
  have eTI : g cTI = nb.2 := by simp [hg, cTI]
  have eC : g (BT + c0) = bitAt (f cTB) (f cTI).toNat := by
    rw [hg, upd_eq _ _ (by unfold BT; omega), upd_eq _ _ (by unfold BT; omega)]; simp [BT]
  -- the global invariant after the three writes, before any mode change (the mode cell is untouched)
  have hgG : ∀ v : Int, (v = mTABLE ∧ nb.1 < 256) ∨ (v = mHDR ∧ nb.1 = 256) → InvG b om lit (Function.update g 0 v) := by
    intro v hv
    have u0 : ∀ c : Int, c ≠ 0 → Function.update g 0 v c = g c := fun c hc => upd_eq _ _ hc
    have hm' : Function.update g 0 v cMODE = v := by simp [cMODE]
    exact {
    n_eq := by rw [u0 _ (by unfold cN; omega), u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)]
               exact hi.1.n_eq
    om_eq := by rw [u0 _ (by unfold cOUTMAX; omega), u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)
                  (by unfold cOUTMAX; omega)]; exact hi.1.om_eq
    x_eq := by rw [u0 _ (by unfold cX; omega), u _ (by unfold cX; omega) (by unfold cX; omega) (by unfold cX; omega)]
               exact hi.1.x_eq
    lit_eq := by rw [u0 _ (by unfold cLIT; omega), u _ (by unfold cLIT; omega) (by unfold cLIT; omega)
                   (by unfold cLIT; omega)]; exact hi.1.lit_eq
    input := fun i a b' => by rw [u0 _ (by omega), u _ (by omega) (by omega) (by omega)]; exact hi.1.input i a b'
    ro := fun i a b' => by
      rw [u0 _ (by unfold X0 at a; omega), u _ (by unfold X0 at a; omega) (by unfold X0 at a; omega)
        (by unfold X0 at a; omega)]; exact hi.1.ro i a b'
    lens := fun j a b' => by rw [u0 _ (by omega), u _ (by omega) (by omega) (by omega)]; exact hi.1.lens j a b'
    tb_rng := fun hm'' => by
      rw [hm'] at hm''
      rw [u0 _ (by unfold cTB; omega), u0 _ (by unfold cTI; omega), eTB, eTI]
      rcases hv with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · rw [h] at hm''; exact absurd hm'' (by decide)
    bits := fun c a b' h3 => by
      rw [u0 _ (by unfold BT; omega)]
      by_cases hc : c = c0
      · subst hc; rw [eC]; exact hbit
      · rw [u _ (by unfold BT; omega) (by unfold BT; omega) (by unfold BT; omega)]
        refine hi.1.bits c a b' (Or.inr ?_)
        rw [hm', u0 _ (by unfold cTB; omega), u0 _ (by unfold cTI; omega), eTB, eTI] at h3
        rcases hv with ⟨h, _⟩ | ⟨h, h2⟩
        · rcases h3 with h3 | h3
          · exact absurd h h3
          · omega
        · omega
    by_rng := by rw [u0 _ (by unfold cBY; omega), u _ (by unfold cBY; omega) (by unfold cBY; omega) (by unfold cBY; omega)]
                 exact hi.1.by_rng
    bi_rng := by rw [u0 _ (by unfold cBI; omega), u _ (by unfold cBI; omega) (by unfold cBI; omega) (by unfold cBI; omega)]
                 exact hi.1.bi_rng
    by_end := by
      rw [u0 _ (by unfold cBY; omega), u _ (by unfold cBY; omega) (by unfold cBY; omega) (by unfold cBY; omega),
        u0 _ (by unfold cBI; omega), u _ (by unfold cBI; omega) (by unfold cBI; omega) (by unfold cBI; omega)]
      exact hi.1.by_end
    m_rng := by rw [u0 _ (by unfold cM; omega), u _ (by unfold cM; omega) (by unfold cM; omega) (by unfold cM; omega)]
                exact hi.1.m_rng
    mode_ok := by rw [hm']; rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
    read_rt := fun hm'' => by rw [hm'] at hm''; rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hm'' <;> simp [mTABLE, mHDR, mREAD] at hm''
    hdr_rng := by
      rw [u0 _ (by unfold cHLIT; omega), u _ (by unfold cHLIT; omega) (by unfold cHLIT; omega) (by unfold cHLIT; omega),
        u0 _ (by unfold cHDIST; omega), u _ (by unfold cHDIST; omega) (by unfold cHDIST; omega) (by unfold cHDIST; omega),
        u0 _ (by unfold cHCLEN; omega), u _ (by unfold cHCLEN; omega) (by unfold cHCLEN; omega) (by unfold cHCLEN; omega)]
      exact hi.1.hdr_rng }
  have hgs : SymsOK b.size om g := by
    intro t q a1 a2 a3 a4
    rw [u _ (by unfold tbase LB0; omega) (by unfold tbase LB0; omega) (by unfold tbase LB0; omega)]
    exact hi.2.syms t q a1 a2 a3 a4
  have hgM : g cMODE = mTABLE := by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
  have hgB : BITS g = BITS f := by
    unfold BITS; rw [u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega),
      u _ (by unfold cBY; omega) (by unfold cBY; omega) (by unfold cBY; omega),
      u _ (by unfold cBI; omega) (by unfold cBI; omega) (by unfold cBI; omega)]
  have hgO : OUT g = OUT f := by
    unfold OUT; rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega),
      u _ (by unfold cM; omega) (by unfold cM; omega) (by unfold cM; omega)]
  have hTf : TBL f = 2048 - c0 := by unfold TBL; rw [if_pos hm]
  have hLf : LOC f = 0 := by unfold LOC; rw [hm]; simp [mTABLE, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX,
    mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD, mHDRD, mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]
  by_cases hend : nb.1 = 256
  · rw [if_pos hend] at hS
    refine ⟨_, Function.update g 0 1, hS, hgw.store (i := 0) (by norm_num) (by unfold L0; omega),
      ⟨hgG 1 (Or.inr ⟨rfl, hend⟩), InvM.mode hgs (by decide) (by decide) (by simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD,
        mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY])⟩, Or.inl ?_⟩
    have u0 : ∀ c : Int, c ≠ 0 → Function.update g 0 1 c = g c := fun c hc => upd_eq _ _ hc
    have hT' : TBL (Function.update g 0 1) = 0 := by unfold TBL; simp [cMODE, mTABLE]
    have hB' : BITS (Function.update g 0 1) = BITS g := by
      unfold BITS; rw [u0 _ (by unfold cN; omega), u0 _ (by unfold cBY; omega), u0 _ (by unfold cBI; omega)]
    have hO' : OUT (Function.update g 0 1) = OUT g := by unfold OUT; rw [u0 _ (by unfold cOUTMAX; omega), u0 _ (by unfold cM; omega)]
    have hL' : LOC (Function.update g 0 1) = 1 := by unfold LOC; simp [cMODE, mHDR]
    unfold Φ mW; rw [hT', hB', hO', hL', hgB, hgO, hTf, hLf]
    have : c0 = 2047 := by omega
    omega
  · rw [if_neg hend] at hS
    have hg0 : Function.update g 0 mTABLE = g := by
      funext c; by_cases hc : c = 0
      · subst hc; simp only [Function.update_self]; exact hgM.symm
      · exact upd_eq _ _ hc
    have hgI : InvG b om lit g := by rw [← hg0]; exact hgG mTABLE (Or.inl ⟨rfl, by omega⟩)
    refine ⟨_, g, hS, hgw, ⟨hgI, {
      syms := hgs
      cur := by rw [hgM]; simp [facts, mTABLE, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP,
        mSYM, mSYMD, mLENX, mDSTD, mDSTX, mCOPY]
      read := fun h => by rw [hgM] at h; simp [mTABLE, mREAD] at h
      ret := fun h => by
        rw [hgM] at h; simp [readRets, mTABLE, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
      dec := fun h => by rw [hgM] at h; simp [mTABLE, mDECODE] at h
      sym := fun h => by rw [hgM] at h; simp [mTABLE, mSYMD, mDSTD, mLSYM] at h
      scopy := fun h => by rw [hgM] at h; simp [mTABLE, mSCOPY] at h
      ralign := fun h => by rw [hgM] at h; simp [mTABLE, mREAD] at h
      align := fun h => by rw [hgM] at h; simp [mTABLE, mSLEN, mSNLEN, mSCOPY] at h }⟩, Or.inl ?_⟩
    have hT' : TBL g = 2048 - (c0 + 1) := by unfold TBL; rw [if_pos hgM, eTB, eTI, hnb1]
    have hL' : LOC g = 0 := by unfold LOC; rw [hgM]; simp [mTABLE, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX,
      mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX, mDSTD, mHDRD, mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]
    unfold Φ mW; rw [hT', hL', hgB, hgO, hTf, hLf]; omega

/-! ## A decode request (SYM, LENX, LENS): the decode cursor at X … X + 3, then mode DECODE -/

def dreqF (g : Int → Int) (X tg rt : Int) : Int → Int :=
  Function.update (Function.update (Function.update (Function.update (Function.update g X 1) (X + 1) 0) (X + 2) tg)
    (X + 3) rt) 0 14

theorem World.dreq {σ : Store} {p : Int} {L : Nat} {g : Int → Int} (hw : World σ p L g) {X : Int} (hX0 : 0 ≤ X)
    (hXL : X + 4 < L) (tg rt : Int) : World ⟨reqDecH σ.H p X tg rt, σ.R⟩ p L (dreqF g X tg rt) := by
  unfold reqDecH dreqF
  exact ((((hw.store (i := X) hX0 (by omega)).store (i := X + 1) (by omega) (by omega)).store (i := X + 2) (by omega)
    (by omega)).store (i := X + 3) (by omega) (by omega)).store (i := 0) (by norm_num) (by omega)

/-- A write to the decode cursor and BUILD's parameters, X … X + 15 (below the read-only area), keeps InvG. -/
theorem InvG.xc {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) {i : Int}
    (h0 : X0 b.size om ≤ i) (h1 : i < X0 b.size om + 16) (v : Int) : InvG b om lit (Function.update f i v) := by
  have hX : (2080 : Int) + b.size + om + 1393 = X0 b.size om := by unfold X0; ring
  have u : ∀ c : Int, c ≠ i → Function.update f i v c = f c := fun c hc => upd_eq f v hc
  exact {
  n_eq := by rw [u _ (by unfold cN; omega)]; exact h.n_eq
  om_eq := by rw [u _ (by unfold cOUTMAX; omega)]; exact h.om_eq
  x_eq := by rw [u _ (by unfold cX; omega)]; exact h.x_eq
  lit_eq := by rw [u _ (by unfold cLIT; omega)]; exact h.lit_eq
  input := fun j a b' => by rw [u _ (by omega)]; exact h.input j a b'
  ro := fun j a b' => by rw [u _ (by omega)]; exact h.ro j a b'
  lens := fun j a b' => by rw [u _ (by omega)]; exact h.lens j a b'
  tb_rng := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm
    rw [u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)]; exact h.tb_rng hm
  bits := fun c a b' h3 => by
    rw [u _ (by unfold cMODE; omega), u _ (by unfold cTB; omega), u _ (by unfold cTI; omega)] at h3
    rw [u _ (by unfold BT; omega)]; exact h.bits c a b' h3
  by_rng := by rw [u _ (by unfold cBY; omega)]; exact h.by_rng
  bi_rng := by rw [u _ (by unfold cBI; omega)]; exact h.bi_rng
  by_end := by rw [u _ (by unfold cBY; omega), u _ (by unfold cBI; omega)]; exact h.by_end
  m_rng := by rw [u _ (by unfold cM; omega)]; exact h.m_rng
  mode_ok := by rw [u _ (by unfold cMODE; omega)]; exact h.mode_ok
  read_rt := fun hm => by
    rw [u _ (by unfold cMODE; omega)] at hm; rw [u _ (by unfold cRET; omega)]; exact h.read_rt hm
  hdr_rng := by
    rw [u _ (by unfold cHLIT; omega), u _ (by unfold cHDIST; omega), u _ (by unfold cHCLEN; omega)]; exact h.hdr_rng }

theorem InvG.dreq {b : Array Nat} {om : Nat} {lit : Bool} {g : Int → Int} (h : InvG b om lit g) (hnt : g cMODE ≠ mTABLE)
    (tg rt : Int) : InvG b om lit (dreqF g (X0 b.size om) tg rt) := by
  unfold dreqF
  refine (((((h.xc (le_refl _) (by omega) _).xc (by omega) (by omega) _).xc (by omega) (by omega) _).xc (by omega)
    (by omega) _).mode (by decide) (by decide) (fun hh => by simp [mDECODE, mREAD] at hh) ?_)
  rw [upd_eq _ _ (by unfold cMODE X0; omega), upd_eq _ _ (by unfold cMODE X0; omega), upd_eq _ _ (by unfold cMODE X0; omega),
    upd_eq _ _ (by unfold cMODE X0; omega)]; exact hnt

theorem InvM.dreq {n om : Nat} {g : Int → Int} (hs : SymsOK n om g) (hhl : 0 ≤ g cHLIT) {tg rt : Int}
    (hpair : (tg = 0 ∧ rt = mLSYM) ∨ (tg = 1 ∧ rt = mSYMD) ∨ (tg = 2 ∧ rt = mDSTD)) (hf : facts n om rt g)
    (hsane : sane n om g tg) : InvM n om (dreqF g (X0 n om) tg rt) := by
  have hX : (2080 : Int) ≤ X0 n om := by unfold X0; omega
  have u : ∀ c : Int, (c < X0 n om ∨ X0 n om + 4 ≤ c) → c ≠ 0 → dreqF g (X0 n om) tg rt c = g c := by
    intro c h1 h2; unfold dreqF
    rw [upd_eq _ _ h2, upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
  have W : Watch n om g (dreqF g (X0 n om) tg rt) :=
    ⟨fun i a b' => (u i (Or.inl b') (by omega)).symm, fun j a b' => (u _ (Or.inr (by omega)) (by unfold X0; omega)).symm,
      fun c hc => by
        simp only [watched, List.mem_cons, List.mem_nil_iff, or_false] at hc
        exact (u c (Or.inl (by omega)) (by omega)).symm⟩
  have hm : dreqF g (X0 n om) tg rt cMODE = 14 := by simp [dreqF, cMODE]
  have hht : 0 ≤ tg ∧ tg ≤ 2 := by omega
  exact {
  syms := fun t q a1 a2 a3 a4 => by rw [u _ (Or.inl (by unfold tbase LB0 X0; omega)) (by unfold tbase LB0; omega)]
                                    exact hs t q a1 a2 a3 a4
  cur := by rw [hm]; simp [facts, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD,
    mLENX, mDSTD, mDSTX, mCOPY]
  read := fun h => by rw [hm] at h; simp [mREAD] at h
  ret := fun h => by
    rw [hm] at h; simp [readRets, mHDRB, mHDRD, mSLEN, mSNLEN, mDH2, mDH3, mDH4, mCLPUT, mLENX, mDSTX, mLREP] at h
  dec := fun _ => by
    have e0 : dreqF g (X0 n om) tg rt (X0 n om) = 1 := by
      unfold dreqF; rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]; simp
    have e2 : dreqF g (X0 n om) tg rt (X0 n om + 2) = tg := by
      unfold dreqF; rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]; simp
    have e3 : dreqF g (X0 n om) tg rt (X0 n om + 3) = rt := by
      unfold dreqF; rw [upd_eq _ _ (by omega)]; simp
    rw [e0, e2, e3]
    exact ⟨facts_congr W hhl hf, le_refl _, by norm_num, hpair, sane_congr W.1 hht.1 hht.2 hsane⟩
  sym := fun h => by rw [hm] at h; simp [mSYMD, mDSTD, mLSYM] at h
  scopy := fun h => by rw [hm] at h; simp [mSCOPY] at h
  ralign := fun h => by rw [hm] at h; simp [mREAD] at h
  align := fun h => by rw [hm] at h; simp [mSLEN, mSNLEN, mSCOPY] at h }

theorem dreq_TBO {b : Array Nat} {om : Nat} {g : Int → Int} (tg rt : Int) :
    TBL (dreqF g (X0 b.size om) tg rt) = 0 ∧ BITS (dreqF g (X0 b.size om) tg rt) = BITS g ∧
      OUT (dreqF g (X0 b.size om) tg rt) = OUT g ∧ LOC (dreqF g (X0 b.size om) tg rt) = 0 := by
  have u : ∀ c : Int, c < 2080 → c ≠ 0 → dreqF g (X0 b.size om) tg rt c = g c := by
    intro c h1 h2; unfold dreqF
    rw [upd_eq _ _ h2, upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by unfold X0; omega),
      upd_eq _ _ (by unfold X0; omega)]
  have hm : dreqF g (X0 b.size om) tg rt cMODE = 14 := by simp [dreqF, cMODE]
  refine ⟨by unfold TBL; rw [hm]; simp [mTABLE], ?_, ?_, ?_⟩
  · unfold BITS; rw [u _ (by unfold cN; omega) (by unfold cN; omega), u _ (by unfold cBY; omega) (by unfold cBY; omega),
      u _ (by unfold cBI; omega) (by unfold cBI; omega)]
  · unfold OUT; rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega), u _ (by unfold cM; omega) (by unfold cM; omega)]
  · unfold LOC; rw [hm]; simp [mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM, mLENX, mSYMD, mSCOPY, mCOPY, mSNLEN, mDSTX,
      mDSTD, mHDRD, mFIXLENS, mBUILD, mLENS, mLSYM, mLREP, mREP, mCLREAD, mCLPUT, mDH4]

theorem safeI_sym {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mSYM) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mSYM, symN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mSYM, symN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hx := hi.1.x_eq
  have hc := hi.2.cur
  rw [hm] at hc; simp only [facts, mSYM, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYMD]
    at hc
  norm_num at hc
  have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (sym_step hw hL (X0 b.size om) hx (by unfold X0; omega) (by unfold X0 L0; omega))
  refine ⟨_, _, hS, hw.dreq (by unfold X0; omega) (by unfold X0 L0; omega) 1 15, ⟨hi.1.dreq hnt 1 15,
    InvM.dreq hi.2.syms hi.1.hdr_rng.1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (by simp only [facts, mSYMD, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM]
          norm_num; exact hc) hc.1⟩, Or.inl ?_⟩
  obtain ⟨t1, t2, t3, t4⟩ := dreq_TBO (b := b) (om := om) (g := f) 1 15
  have hLf : LOC f = 1 := by unfold LOC; rw [hm]; simp [mSYM, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3]
  have hTf : TBL f = 0 := by unfold TBL; rw [if_neg hnt]
  unfold Φ mW; rw [t1, t2, t3, t4, hLf, hTf]; omega

theorem safeI_lenx {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mLENX) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mLENX, lenxN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mLENX, lenxN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hx := hi.1.x_eq
  have hc := hi.2.cur
  rw [hm] at hc; simp only [facts, mLENX, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM,
    mSYMD, mDSTD, mDSTX] at hc
  norm_num at hc
  have hacc := hi.2.ret (by rw [hm]; decide)
  set g := Function.update f 5 (f cPEND + f cACC) with hg
  have hsg : ∀ t : Int, 0 ≤ t → t ≤ 2 → sane b.size om f t → sane b.size om g t := fun t a b' h =>
    sane_congr (fun i h1 _ => (upd_eq f _ (by omega)).symm) a b' h
  have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
    (lenx_step hw hL (X0 b.size om) (f cACC) (f cPEND) hx (by unfold X0; omega) (by unfold X0 L0; omega) rfl rfl)
  have hgw := (hw.store (i := 5) (by norm_num) (by omega) (v := f cPEND + f cACC)).dreq (X := X0 b.size om)
    (by unfold X0; omega) (by unfold X0 L0; omega) 2 17
  have hnt' : g cMODE ≠ mTABLE := by rw [hg, upd_eq _ _ (by unfold cMODE; omega)]; exact hnt
  refine ⟨_, _, hS, hgw, ⟨(hi.1.upd (by unfold scratch; omega) _).dreq hnt' 2 17,
    InvM.dreq (SymsOK.upd hi.2.syms (by norm_num) _) (by rw [upd_eq _ _ (by unfold cHLIT; omega)]; exact hi.1.hdr_rng.1)
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (by simp only [facts, mDSTD, mSNLEN, mSCOPY, mFIXLENS, mBUILD, mCLREAD, mCLPUT, mLENS, mLSYM, mLREP, mREP, mSYM, mSYMD,
            mLENX]
          norm_num
          refine ⟨hsg 1 (by norm_num) (by norm_num) hc.1, hsg 2 (by norm_num) (by norm_num) hc.2.1, ?_⟩
          simp [cPEND] at hc ⊢; rw [hm] at hacc; omega)
      (hsg 2 (by norm_num) (by norm_num) hc.2.1)⟩, Or.inl ?_⟩
  obtain ⟨t1, t2, t3, t4⟩ := dreq_TBO (b := b) (om := om) (g := g) 2 17
  have hB : BITS g = BITS f := by
    unfold BITS; rw [hg, upd_eq _ _ (by unfold cN; omega), upd_eq _ _ (by unfold cBY; omega), upd_eq _ _ (by unfold cBI; omega)]
  have hO : OUT g = OUT f := by unfold OUT; rw [hg, upd_eq _ _ (by unfold cOUTMAX; omega), upd_eq _ _ (by unfold cM; omega)]
  have hLf : LOC f = 1 := by unfold LOC; rw [hm]; simp [mLENX, mHDR, mHDRB, mSHDR, mSLEN, mDHDR, mDH2, mDH3, mSYM]
  have hTf : TBL f = 0 := by unfold TBL; rw [if_neg hnt]
  unfold Φ mW; rw [t1, t2, t3, t4, hB, hO, hLf, hTf]; omega

end VIRDeflate.Step
