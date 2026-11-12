/-
  O95, K5-2b (k5/RANGE-SITES.md): CLREAD and CLPUT in range from Inv alone (n, OUTMAX < 2³²). Both read the read-only
  ORDER table at X + 134 + i; its value is in [0, 18] by Safety's `ro` and `order_rng`, as `safeI_clread` reads it.
-/
import K5.Safe2

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

theorem order_cell (hi : Inv b om lit f) (h0 : 0 ≤ f cFILL) (h19 : f cFILL < 19) :
    0 ≤ f (X0 b.size om + 134 + f cFILL) ∧ f (X0 b.size om + 134 + f cFILL) ≤ 18 := by
  rw [hi.1.ro _ (by omega) (by omega)]
  exact order_rng b om lit _ h0 h19

theorem clread_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mCLREAD) : SrcInRange (closeAt p clreadT, σ) := by
  have hc := hi.2.cur
  rw [hm, facts_clread] at hc
  obtain ⟨hf0, hf19, hc4, _, _⟩ := hc
  have hh := hi.1.hdr_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  by_cases hlt : f cFILL < f cHCLEN
  · apply clread_req_inR hw (by unfold L0; omega) _ _ _ _ _ rfl rfl hx hn ho hlt
    all_goals (try rw [hL0]); all_goals (try unfold X0)
    rclose
  · by_cases h19 : f cFILL < 19
    · have hor := order_cell hi hf0 h19
      apply clread_zero_inR hw (by unfold L0; omega) _ _ _ _ _ _ rfl rfl hx hn ho hlt h19 hf0 (by unfold X0; omega)
        (by rw [hL0]; unfold X0; omega) rfl (by omega) (by rw [hL0]; omega)
      all_goals (have hor' := hor; unfold X0 at hor')
      all_goals (try rw [hL0]); all_goals (try unfold X0)
      rclose
    · apply clread_end_inR hw (by unfold L0; omega) _ _ _ _ _ rfl rfl hx hn ho hlt h19 (by unfold X0; omega)
        (by rw [hL0]; unfold X0; omega)
      all_goals (try rw [hL0]); all_goals (try unfold X0)
      rclose

theorem clput_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mCLPUT) : SrcInRange (closeAt p clputT, σ) := by
  have hc := hi.2.cur
  rw [hm] at hc
  simp only [facts, show mCLPUT ≠ mSNLEN by decide, show mCLPUT ≠ mSCOPY by decide, show mCLPUT ≠ mFIXLENS by decide,
    show mCLPUT ≠ mBUILD by decide, show mCLPUT ≠ mCLREAD by decide, if_false, if_true] at hc
  obtain ⟨hf0, hf19, _, _, _, _⟩ := hc
  have ha := acc_rng hi (by rw [hm]; decide)
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hor := order_cell hi hf0 hf19
  apply clput_step_inR hw (by unfold L0; omega) _ _ _ _ _ _ rfl hx hn ho rfl hf0 hf19 (by unfold X0; omega)
    (by rw [hL0]; unfold X0; omega) rfl (by omega) (by rw [hL0]; omega)
  all_goals (have hor' := hor; unfold X0 at hor')
  all_goals (try rw [hL0]); all_goals (try unfold X0)
  rclose

end K5
