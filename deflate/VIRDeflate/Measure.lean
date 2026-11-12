/-
OBJECT-DEFLATE under X1 (a): Safety's MEASURE (DECLARATIONS-DEFLATE.md S-16), written HERE BEFORE any proof that uses it.
D3 scores it. `Φ = W · (TBL + BITS + OUT) + LOC`, W = 4096, over the cell function `f` of the world:
- TBL  the bit table's cells still to fill (mode TABLE only);
- BITS the input bits not yet consumed, 8·(n − by) − bi;
- OUT  OUTMAX − m — the OUTPUT side, which D3 predicts the proved measure involves;
- LOC  the bookkeeping steps left before the next step that fills a table cell, consumes a bit or writes an output byte.
`N n om = W · (2048 + 8n + om)` is Safety's bound (`Φ` of the initial world). No proof in this file.
-/
import VIRDeflate.Fit

namespace VIRDeflate.Step
open VIRL1 VIRL2

def mW : Int := 4096

/-- A full BUILD for nn symbols: ZERO 16 + 1, COUNT nn + 1, NEXT 15 + 1, LEFT 15 + 1, SYMS nn + 1. -/
def bfull (nn : Int) : Int := 2 * nn + 51

/-- The rest of the current BUILD at phase ph, index j (ZERO and COUNT and SYMS count from 0; NEXT and LEFT from 1). -/
def bRem (ph j nn : Int) : Int :=
  if ph = 0 then (16 - j) + 1 + (nn + 1) + 16 + 16 + (nn + 1)
  else if ph = 1 then (nn - j) + 1 + 16 + 16 + (nn + 1)
  else if ph = 2 then (16 - j) + 1 + 16 + (nn + 1)
  else if ph = 3 then (16 - j) + 1 + (nn + 1)
  else (nn - j) + 1

/-- The L build, the D build, then SYM: what follows the last length of a block's code lengths. -/
def chainLD (hl hd : Int) : Int := bfull hl + bfull hd + 1

/-- CLREAD at fill index i: a request when i < HCLEN; otherwise the zero-fill to 19, the CL build, then LENS. -/
def locCL (i hc hl hd : Int) : Int := if i < hc then 1 else (19 - i) + 1 + bfull 19 + (1 + chainLD hl hd)

/-- FIXLENS at fill index i: the rest of S5's 318 lengths, then the fixed L (288) and D (30) builds, then SYM. -/
def locFIX (i : Int) : Int := (318 - i) + 1 + bfull 288 + bfull 30 + 1

/-- LOC, per mode (S-16). -/
def LOC (f : Int → Int) : Int :=
  let md := f cMODE
  let hl := f cHLIT
  let hd := f cHDIST
  if md = mHDR ∨ md = mHDRB ∨ md = mSHDR ∨ md = mSLEN ∨ md = mDHDR ∨ md = mDH2 ∨ md = mDH3 ∨ md = mSYM ∨ md = mLENX then 1
  else if md = mSYMD ∨ md = mSCOPY ∨ md = mCOPY then 2
  else if md = mSNLEN ∨ md = mDSTX then 3
  else if md = mDSTD then 4
  else if md = mHDRD then 1 + locFIX 0
  else if md = mFIXLENS then locFIX (f cFILL)
  else if md = mBUILD then
    bRem (f cPHASE) (f cINDEX) (f (f cX + 6)) +
      (if f cTGT = 0 then 1 + chainLD hl hd else if f cTGT = 1 then bfull hd + 1 else 1)
  else if md = mLENS then 1 + chainLD hl hd
  else if md = mLSYM then 2 + chainLD hl hd
  else if md = mLREP then 3 + chainLD hl hd + (hl + hd - f cFILL)
  else if md = mREP then f cPEND + 2 + chainLD hl hd
  else if md = mCLREAD then locCL (f cFILL) (f cHCLEN) hl hd
  else if md = mCLPUT then 1 + locCL (f cFILL + 1) (f cHCLEN) hl hd
  else if md = mDH4 then 1 + (20 + bfull 19 + (1 + chainLD hl hd))
  else 0      -- TABLE, READ, DECODE, DONE, REJECT

def TBL (f : Int → Int) : Int := if f cMODE = mTABLE then 2048 - (8 * f cTB + f cTI) else 0
def BITS (f : Int → Int) : Int := 8 * (f cN - f cBY) - f cBI
def OUT (f : Int → Int) : Int := f cOUTMAX - f cM

/-- **The measure D3 scores.** -/
def Φ (f : Int → Int) : Int := mW * (TBL f + BITS f + OUT f) + LOC f

/-- **Safety's bound:** `Φ` of the initial world, a function of n and OUTMAX alone. -/
def Nbound (n om : Nat) : Nat := 4096 * (2048 + 8 * n + om)

end VIRDeflate.Step
