/-
  O95, K5-2b (k5/RANGE-SITES.md), the Modes1 group that Safety's `Inv` bounds alone, with n, OUTMAX < 2³² (K5's premise):
  HDRB · HDRD · SLEN · DHDR · SHDR · DH2 · DH3 · DH4 · FIXLENS · TABLE. Each wrapper takes the trace's facts from `Inv`
  as Safety's own `safeI_*` takes them, and closes every range obligation by `inRange_eq` and linear arithmetic.
  SNLEN (`cPEND` unbounded above in Inv, finding K5-2-0) and CLPUT (reads the read-only ORDER table) are not here.
-/
import K5.SafeRead
import K5.Table

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

/-- Every range obligation left by `apply <trace>`: an equation closed by `rfl`, a bound by `omega`, a range by `inRange_eq`. -/
macro "rclose" : tactic => `(tactic| all_goals first | (apply inRange_eq <;> omega) | omega | rfl)

theorem acc_rng {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (hi : Inv b om lit f) (h : f cMODE ∈ readRets) :
    0 ≤ f cACC ∧ f cACC ≤ 65536 := by
  have := hi.2.ret h
  have := kcap_le (f cMODE)
  omega

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

theorem hdrb_inR (hw : World σ p (L0 b.size om) f) : SrcInRange (closeAt p hdrbT, σ) :=
  hdrb_step_inR hw (by unfold L0; omega) _ rfl

theorem hdrd_inR (hw : World σ p (L0 b.size om) f) : SrcInRange (closeAt p hdrdT, σ) :=
  hdrd_step_inR hw (by unfold L0; omega) _ rfl

theorem slen_inR (hw : World σ p (L0 b.size om) f) : SrcInRange (closeAt p slenT, σ) :=
  slen_step_inR hw (by unfold L0; omega) _ rfl

theorem dhdr_inR (hw : World σ p (L0 b.size om) f) : SrcInRange (closeAt p dhdrT, σ) :=
  dhdr_step_inR hw (by unfold L0; omega)

theorem shdr_inR (hn32 : b.size < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) :
    SrcInRange (closeAt p shdrT, σ) := by
  have := hi.1.by_rng
  apply shdr_step_inR hw (by unfold L0; omega) _ _ rfl rfl
  rclose

theorem dh2_inR (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDH2) :
    SrcInRange (closeAt p dh2T, σ) := by
  have := acc_rng hi (by rw [hm]; decide)
  apply dh2_step_inR hw (by unfold L0; omega) _ rfl
  rclose

theorem dh3_inR (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDH3) :
    SrcInRange (closeAt p dh3T, σ) := by
  have := acc_rng hi (by rw [hm]; decide)
  apply dh3_step_inR hw (by unfold L0; omega) _ rfl
  rclose

theorem dh4_inR (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mDH4) :
    SrcInRange (closeAt p dh4T, σ) := by
  have := acc_rng hi (by rw [hm]; decide)
  apply dh4_step_inR hw (by unfold L0; omega) _ _ _ rfl rfl rfl
  rclose

theorem fixlens_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mFIXLENS) : SrcInRange (closeAt p fixlensT, σ) := by
  have hfl : 0 ≤ f cFILL ∧ f cFILL ≤ 318 := by
    have := hi.2.cur; rw [hm] at this; simpa [facts, mFIXLENS, mSNLEN, mSCOPY] using this
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  by_cases h318 : f cFILL = 318
  · apply fixlens_end_inR hw (by unfold L0; omega) _ _ _ _ h318 rfl rfl rfl rfl
    all_goals (try rw [hx]); all_goals (try rw [hn]); all_goals (try rw [ho]); all_goals (try unfold X0); all_goals (try unfold L0)
    rclose
  · apply fixlens_step_inR hw (f cFILL).toNat b.size om (by unfold L0; omega) (by omega) (by omega) hn ho
    rclose

theorem table_inv_inR (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mTABLE) :
    SrcInRange (closeAt p tableT, σ) := by
  obtain ⟨h0, h1, h2, h3⟩ := hi.1.tb_rng hm
  exact table_inR hw (by unfold L0; omega) (f cTB).toNat (f cTI).toNat (by omega) (by omega) (by omega) (by omega)

end K5
