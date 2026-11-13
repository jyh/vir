/-
  O95, K5-2: `step_inrange` — DEFLATE's step term is in range on every world satisfying Safety's `Inv` and K5's `Mag`, for
  n, OUTMAX < 2³² and bytes < 256. Dispatch's `step_inR` plus the 28 Safety-level wrappers (k5/K5/Safe*.lean, Mag.lean,
  SafeBuild.lean). With `Mag_step` (owed) this is K5-2's `deflate_inrange` over every reachable world.
-/
import K5.SafeBuild
import K5.Dispatch

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

theorem step_inrange {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hb : ∀ x ∈ b, x < 256) (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32)
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) :
    SrcInRange (closeAt p stepT, σ) := by
  refine step_inR hw (by unfold L0; omega) (f cMODE) rfl ?_
  intro t ht
  have hmode := hi.1.mode_ok
  simp only [validModes, List.mem_cons, List.mem_nil_iff, or_false] at hmode
  rcases hmode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hm : f cMODE = mTABLE := by rw [h]; rfl
    rw [h, show modes.lookup (0 : Int) = some tableN from rfl] at ht
    cases ht
    exact table_inv_inR hw hi hm
  · have hm : f cMODE = mHDR := by rw [h]; rfl
    rw [h, show modes.lookup (1 : Int) = some hdrN from rfl] at ht
    cases ht
    exact hdr_inR hw (by unfold L0; omega)
  · have hm : f cMODE = mREAD := by rw [h]; rfl
    rw [h, show modes.lookup (2 : Int) = some readN from rfl] at ht
    cases ht
    exact read_inR hb hn32 hw hi hm
  · have hm : f cMODE = mHDRB := by rw [h]; rfl
    rw [h, show modes.lookup (3 : Int) = some hdrbN from rfl] at ht
    cases ht
    exact hdrb_inR hw
  · have hm : f cMODE = mHDRD := by rw [h]; rfl
    rw [h, show modes.lookup (4 : Int) = some hdrdN from rfl] at ht
    cases ht
    exact hdrd_inR hw
  · have hm : f cMODE = mSHDR := by rw [h]; rfl
    rw [h, show modes.lookup (5 : Int) = some shdrN from rfl] at ht
    cases ht
    exact shdr_inR hn32 hw hi
  · have hm : f cMODE = mFIXLENS := by rw [h]; rfl
    rw [h, show modes.lookup (6 : Int) = some fixlensN from rfl] at ht
    cases ht
    exact fixlens_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mDHDR := by rw [h]; rfl
    rw [h, show modes.lookup (7 : Int) = some dhdrN from rfl] at ht
    cases ht
    exact dhdr_inR hw
  · have hm : f cMODE = mSLEN := by rw [h]; rfl
    rw [h, show modes.lookup (8 : Int) = some slenN from rfl] at ht
    cases ht
    exact slen_inR hw
  · have hm : f cMODE = mSNLEN := by rw [h]; rfl
    rw [h, show modes.lookup (9 : Int) = some snlenN from rfl] at ht
    cases ht
    exact snlen_inR hn32 hom32 hw hi hg hm
  · have hm : f cMODE = mSCOPY := by rw [h]; rfl
    rw [h, show modes.lookup (10 : Int) = some scopyN from rfl] at ht
    cases ht
    exact scopy_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mBUILD := by rw [h]; rfl
    rw [h, show modes.lookup (11 : Int) = some buildN from rfl] at ht
    cases ht
    exact build_inR hn32 hom32 hw hi hg hm
  · have hm : f cMODE = mLENS := by rw [h]; rfl
    rw [h, show modes.lookup (12 : Int) = some lensN from rfl] at ht
    cases ht
    exact lens_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mSYM := by rw [h]; rfl
    rw [h, show modes.lookup (13 : Int) = some symN from rfl] at ht
    cases ht
    exact sym_inR hn32 hom32 hw hi
  · have hm : f cMODE = mDECODE := by rw [h]; rfl
    rw [h, show modes.lookup (14 : Int) = some decodeN from rfl] at ht
    cases ht
    exact decode_inR hb hn32 hom32 hw hi hg hm
  · have hm : f cMODE = mSYMD := by rw [h]; rfl
    rw [h, show modes.lookup (15 : Int) = some symdN from rfl] at ht
    cases ht
    exact symd_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mLENX := by rw [h]; rfl
    rw [h, show modes.lookup (16 : Int) = some lenxN from rfl] at ht
    cases ht
    exact lenx_inR hn32 hom32 hw hi hg hm
  · have hm : f cMODE = mDSTD := by rw [h]; rfl
    rw [h, show modes.lookup (17 : Int) = some dstdN from rfl] at ht
    cases ht
    exact dstd_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mDSTX := by rw [h]; rfl
    rw [h, show modes.lookup (18 : Int) = some dstxN from rfl] at ht
    cases ht
    exact dstx_inR hn32 hom32 hw hi hg hm
  · have hm : f cMODE = mCOPY := by rw [h]; rfl
    rw [h, show modes.lookup (19 : Int) = some copyN from rfl] at ht
    cases ht
    exact copy_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mDH2 := by rw [h]; rfl
    rw [h, show modes.lookup (20 : Int) = some dh2N from rfl] at ht
    cases ht
    exact dh2_inR hw hi hm
  · have hm : f cMODE = mDH3 := by rw [h]; rfl
    rw [h, show modes.lookup (21 : Int) = some dh3N from rfl] at ht
    cases ht
    exact dh3_inR hw hi hm
  · have hm : f cMODE = mDH4 := by rw [h]; rfl
    rw [h, show modes.lookup (22 : Int) = some dh4N from rfl] at ht
    cases ht
    exact dh4_inR hw hi hm
  · have hm : f cMODE = mCLREAD := by rw [h]; rfl
    rw [h, show modes.lookup (23 : Int) = some clreadN from rfl] at ht
    cases ht
    exact clread_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mCLPUT := by rw [h]; rfl
    rw [h, show modes.lookup (24 : Int) = some clputN from rfl] at ht
    cases ht
    exact clput_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mLSYM := by rw [h]; rfl
    rw [h, show modes.lookup (25 : Int) = some lsymN from rfl] at ht
    cases ht
    exact lsym_inR hn32 hom32 hw hi hm
  · have hm : f cMODE = mLREP := by rw [h]; rfl
    rw [h, show modes.lookup (26 : Int) = some lrepN from rfl] at ht
    cases ht
    exact lrep_inR hw hi hg hm
  · have hm : f cMODE = mREP := by rw [h]; rfl
    rw [h, show modes.lookup (27 : Int) = some repN from rfl] at ht
    cases ht
    exact rep_inR hn32 hom32 hw hi hm
  · rw [h, show modes.lookup (98 : Int) = none from rfl] at ht
    cases ht
  · rw [h, show modes.lookup (99 : Int) = none from rfl] at ht
    cases ht

end K5
