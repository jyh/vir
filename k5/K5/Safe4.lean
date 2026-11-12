/-
  O95, K5-2b (k5/RANGE-SITES.md): LENS · LSYM · SYMD in range from Inv alone (n, OUTMAX < 2³²): fill and the two header
  counts from `facts_lens`/`facts_lsym`, the decoded symbol at X + 4 from InvM `sym` (0 ≤ s < 288), M from `m_rng`.
-/
import K5.Safe3

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

theorem lens_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mLENS) : SrcInRange (closeAt p lensT, σ) := by
  have hc := hi.2.cur
  rw [hm, facts_lens] at hc
  obtain ⟨hf0, hfh, hl286, hd30, _⟩ := hc
  have hh := hi.1.hdr_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  by_cases hlt : f cFILL < f cHLIT + f cHDIST
  · apply lens_req_inR hw (by unfold L0; omega) _ _ _ _ _ _ rfl rfl rfl hx hn ho hlt (by unfold X0; omega)
      (by rw [hL0]; unfold X0; omega)
    all_goals (try rw [hL0]); all_goals (try unfold X0)
    rclose
  · apply lens_end_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ rfl rfl rfl hx hn ho hlt (by unfold X0; omega)
      (by rw [hL0]; unfold X0; omega) (by omega) (by rw [hL0]; omega) rfl
    all_goals (try rw [hL0]); all_goals (try unfold X0)
    rclose

theorem lsym_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mLSYM) : SrcInRange (closeAt p lsymT, σ) := by
  have hc := hi.2.cur
  rw [hm, facts_lsym] at hc
  obtain ⟨hf0, hfh, hl286, hd30, _⟩ := hc
  have hh := hi.1.hdr_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  have hs := hi.2.sym (Or.inr (Or.inr hm))
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  apply lsym_step_inR hw (by unfold L0; omega) _ _ _ _ _ _ hx (by unfold X0; omega) (by rw [hL0]; unfold X0; omega) rfl rfl
    hn ho (fun _ => ⟨by omega, by rw [hL0]; omega⟩) (fun _ _ => ⟨by omega, by rw [hL0]; omega⟩) rfl
  all_goals (have hs' := hs; unfold X0 at hs')
  all_goals (try rw [hL0]); all_goals (try unfold X0)
  rclose

theorem symd_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hm : f cMODE = mSYMD) : SrcInRange (closeAt p symdT, σ) := by
  have hmr := hi.1.m_rng
  have hn := hi.1.n_eq
  have ho := hi.1.om_eq
  have hx := hi.1.x_eq
  have hs := hi.2.sym (Or.inl hm)
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  apply symd_step_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ _ hx (by unfold X0; omega) (by rw [hL0]; unfold X0; omega) rfl
    rfl ho hn rfl (fun _ _ => ⟨by omega, by rw [hL0]; omega⟩) rfl rfl
  all_goals (have hs' := hs; unfold X0 at hs')
  all_goals (try rw [hL0]); all_goals (try unfold X0)
  rclose

end K5
