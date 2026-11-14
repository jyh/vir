/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): DEFLATE's step over ⟶₅. `stepT₅` loads MODE and dispatches
  over the 28 modes exactly as `dispN modes` does. SCOPY, COPY, REP, FIXLENS, READ and DECODE are their Tm₅ terms, entered under
  the mode binder by `shift 0`. BUILD's phase dispatch enters zeroT₅ at phase 0 and keeps phases 1–4 as DEFLATE's own NT. Every
  other mode is DEFLATE's branch `t.c ["md", "w"]`, lifted by ι. `stepS₅` and `iterS₅` are `stepS` and `iterS` over run₅, at the
  same KSTEP and the same world capability; the statements are Statements.lean's, word for word, over `iterS₅`. Beside them,
  owed item (i) of the addendum: World and Sole determine the store.
-/
import VIRL5.Shift5
import VIRL5.Bridge5
import VIRL5.Lift5
import VIRL5.Scopy5
import VIRL5.Copy5
import VIRL5.Rep5
import VIRL5.Zero5
import VIRL5.Fixlens5
import VIRL5.Read5
import VIRL5.Decode5
import VIRDeflate.Dispatch

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A DEFLATE mode branch, as DEFLATE's dispatch compiles it (mode at #0, world at #1), lifted to ⟶₅. -/
def lift₅ (t : NT) : Tm₅ := ιE (t.c ["md", "w"])

/-- BUILD phases 1–4 as DEFLATE writes them (phase at #0, world at #1). -/
def buildRestN : NT :=
  .ite (.p2 .eq (.v "ph") (.i 1)) bCountN <|
  .ite (.p2 .eq (.v "ph") (.i 2)) bNextN bRestN

/-- BUILD over ⟶₅ (world at #0): phase 0 is zeroT₅, phases 1–4 are DEFLATE's own. -/
def buildT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cPHASE)] t5int
    (.ite (.prim .eq [.var 0, .const (.int 0)]) (zeroT₅.shift 0) (ιE (buildRestN.c ["ph", "w"])))

/-- The 28 modes in DEFLATE's order (`modes`), six re-expressed and BUILD's phase 0. -/
def modes₅ : List (Int × Tm₅) :=
  [(mTABLE, lift₅ tableN), (mHDR, lift₅ hdrN), (mREAD, readT₅.shift 0), (mHDRB, lift₅ hdrbN), (mHDRD, lift₅ hdrdN),
   (mSHDR, lift₅ shdrN), (mFIXLENS, fixlensT₅.shift 0), (mDHDR, lift₅ dhdrN), (mSLEN, lift₅ slenN), (mSNLEN, lift₅ snlenN),
   (mSCOPY, scopyT₅.shift 0), (mBUILD, buildT₅.shift 0), (mLENS, lift₅ lensN), (mSYM, lift₅ symN),
   (mDECODE, decodeT₅.shift 0), (mSYMD, lift₅ symdN), (mLENX, lift₅ lenxN), (mDSTD, lift₅ dstdN), (mDSTX, lift₅ dstxN),
   (mCOPY, copyT₅.shift 0), (mDH2, lift₅ dh2N), (mDH3, lift₅ dh3N), (mDH4, lift₅ dh4N), (mCLREAD, lift₅ clreadN),
   (mCLPUT, lift₅ clputN), (mLSYM, lift₅ lsymN), (mLREP, lift₅ lrepN), (mREP, repT₅.shift 0)]

/-- The dispatch, as `dispN`: an unmatched mode returns the world unchanged. -/
def disp₅ : List (Int × Tm₅) → Tm₅
  | [] => .ret (.var 1)
  | (k, t) :: r => .ite (.prim .eq [.var 0, .const (.int k)]) t (disp₅ r)

/-- ONE step of the program over ⟶₅ (world at #0). -/
def stepT₅ : Tm₅ := .letOp .load [.var 0, .const (.int cMODE)] t5int (disp₅ modes₅)

/-- The world capability a finished ⟶₅ configuration returns, if any (`ret a` or `ret a []`). -/
def capOf₅ : Tm₅ → Option Int
  | .ret a => match a.eval with | some (.const (.cap q)) => some q | _ => none
  | .retK a [] => match a.eval with | some (.const (.cap q)) => some q | _ => none
  | _ => none

/-- ONE step from σ, as `stepS`: `some σ'` when the step returns the same world capability ⟨p⟩ within KSTEP, else `none`. -/
def stepS₅ (p : Int) (σ : Store) : Option Store :=
  match capOf₅ (run₅ KSTEP (stepT₅.subst 0 (.const (.cap p)), σ)).1 with
  | some q => if q = p then some (run₅ KSTEP (stepT₅.subst 0 (.const (.cap p)), σ)).2 else none
  | none => none

/-- k steps. -/
def iterS₅ (p : Int) : Nat → Store → Option Store
  | 0, σ => some σ
  | k + 1, σ => (stepS₅ p σ).bind (iterS₅ p k)

/-- **SAFETY over ⟶₅**: Statements.lean's `SafetyStmt`, with `iterS₅` for `iterS`. -/
def SafetyStmt₅ : Prop :=
  ∃ N : Nat → Nat → Nat, ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int), (∀ x ∈ b, x < 256) →
    ∃ k σ', k ≤ N b.size om ∧ iterS₅ p k (initStore b om lit p) = some σ' ∧
      (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT)

/-- **CORRECTNESS over ⟶₅**: Statements.lean's `CorrectStmt`, with `iterS₅` for `iterS`. -/
def CorrectStmt₅ : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int), (∀ x ∈ b, x < 256) →
    (∀ o, (∃ k σ', iterS₅ p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mDONE ∧ outOf p b.size σ' = o) ↔
      VIRDeflate.run lit b om = .ok o) ∧
    ((∃ k σ', iterS₅ p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mREJECT) ↔ ∃ r, VIRDeflate.run lit b om = .error r)

/-- **Owed (i): World and Sole determine the store.** Two stores that each own only the region at p, with the same contents,
  are equal. -/
theorem sole_world_eq {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int}
    (hw : World σ p L f) (hs : Sole σ p L) (hw' : World σ' p L f) (hs' : Sole σ' p L) : σ = σ' := by
  obtain ⟨H, R⟩ := σ
  obtain ⟨H', R'⟩ := σ'
  obtain ⟨hR0, hH0⟩ := hs
  obtain ⟨hR0', hH0'⟩ := hs'
  have hR : R = Finmap.singleton p L := hR0
  have hR' : R' = Finmap.singleton p L := hR0'
  have hH : ∀ a, ¬ Store.InRegion a p L → H.lookup a = none := hH0
  have hH' : ∀ a, ¬ Store.InRegion a p L → H'.lookup a = none := hH0'
  have eH : H = H' := by
    apply Finmap.ext_lookup
    intro a
    by_cases ha : Store.InRegion a p L
    · have ha' := ha
      simp only [Store.InRegion] at ha'
      have h1 : H.lookup (p + (a - p)) = some (f (a - p)) := hw.cell (a - p) (by omega) (by omega)
      have h2 : H'.lookup (p + (a - p)) = some (f (a - p)) := hw'.cell (a - p) (by omega) (by omega)
      rw [show p + (a - p) = a by omega] at h1 h2
      rw [h1, h2]
    · rw [hH a ha, hH' a ha]
  rw [eH, hR, hR']

/-- The branch the dispatch reaches for a re-expressed mode is that mode's own term at ⟨p⟩. -/
theorem branch_shift₅ (t : Tm₅) (p : Int) (m : Int) :
    ((t.shift 0).subst 1 (.const (.cap p))).subst 0 (.const (.int m)) = t.subst 0 (.const (.cap p)) :=
  shift_branch₅ t p _

end VIRL5
