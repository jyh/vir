/-
  O95, K5-2b (k5/RANGE-SITES.md), the Modes2 group that Safety's `Inv` bounds alone (n, OUTMAX < 2³²): SCOPY · COPY · REP ·
  SYM · DSTD. Facts are read as Safety's `safeI_*` reads them (`facts_*`, `m_rng`, `hdr_rng`, InvM `scopy`/`sym`).
  LENX, DSTX, LREP (and SNLEN in Modes1) read `cPEND`/`cDIST`, which Inv leaves unbounded above (finding K5-2-0): not here.
-/
import K5.Safe1
import VIRDeflate.Safety

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

theorem scopy_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mSCOPY) : SrcInRange (closeAt p scopyT, σ) := by
  have hc := hi.2.cur
  rw [hm] at hc
  simp only [facts, show mSCOPY ≠ mSNLEN by decide, if_false, if_true] at hc
  have hsc := hi.2.scopy hm
  have hmr := hi.1.m_rng
  have hbr := hi.1.by_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  by_cases hk : f cPEND = 0
  · exact scopy_end_inR hw (by unfold L0; omega) _ hk rfl
  · apply scopy_byte_inR hw (f cBY).toNat b.size (f cM).toNat om _ _ (by unfold L0; omega) rfl hk (by omega) hn (by omega)
      (by rw [show (((f cBY).toNat : Nat) : Int) = f cBY by omega]) (by omega) (by omega)
    rclose

theorem copy_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mCOPY) : SrcInRange (closeAt p copyT, σ) := by
  have hc := hi.2.cur
  rw [hm, facts_copy] at hc
  obtain ⟨_, _, hp0, hd0, hdm, hmp⟩ := hc
  have hmr := hi.1.m_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  by_cases hpd : f cPEND = 0
  · exact copy_end_inR hw (by unfold L0; omega) hpd
  · apply copy_byte_inR hw (by unfold L0; omega) _ _ _ _ _ rfl hpd hn rfl rfl
    all_goals (try rw [hL0])
    rclose

theorem rep_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mREP) : SrcInRange (closeAt p repT, σ) := by
  have hc := hi.2.cur
  rw [hm, facts_rep] at hc
  obtain ⟨hf0, hp0, hfp, hl286, hd30, _, hla0, hla15⟩ := hc
  have hh := hi.1.hdr_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  by_cases hpd : f cPEND = 0
  · exact rep_end_inR hw (by unfold L0; omega) hpd
  · apply rep_byte_inR hw (by unfold L0; omega) _ _ _ _ _ rfl hpd rfl rfl hn ho
    all_goals (try rw [hL0])
    rclose

theorem sym_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) :
    SrcInRange (closeAt p symT, σ) := by
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  apply sym_step_inR hw (by unfold L0; omega) _ hx
  all_goals (try rw [hL0]); all_goals (try unfold X0)
  rclose

theorem dstd_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mDSTD) : SrcInRange (closeAt p dstdT, σ) := by
  have hx := hi.1.x_eq
  have hs := hi.2.sym (Or.inr (Or.inl hm))
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  apply dstd_step_inR hw (by unfold L0; omega) _ _ _ _ hx (by unfold X0; omega) (by rw [hL0]; unfold X0; omega)
    rfl hs.1 rfl rfl
  all_goals (have hs' := hs; unfold X0 at hs')
  all_goals (try rw [hL0]); all_goals (try unfold X0)
  rclose

end K5
