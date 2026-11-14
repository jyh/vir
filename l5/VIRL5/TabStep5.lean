/-
  O95 layer L5, Lean arm (STATUS 323, fork (T)): **every DEFLATE step keeps (T)**, by the mode Inv allows (`mode_ok`): TABLE by
  `table_one` (the counter advances, or HDR with all 2,048 bits); DONE and REJECT are fixpoints; the fourteen modes whose stores
  are all constant cells by the generic frame (`stepS_tkeep`); the thirteen others by their own step lemmas (TabChunk5,
  TabDec5, TabBuild5). Then the iterate keeps it (`iterS_tab`), from the initial world (`tab_init`).
-/
import VIRL5.TabBuild5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A mode whose body passes `tkT` keeps Tab. -/
theorem tab_tk {b : Array Nat} {om : Nat} {p : Int} {σ σ' : Store} {f f' : Int → Int} {k : Int} {t : NT}
    (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hm : f cMODE = k) (hk : modes.lookup k = some t)
    (htk : tkT (t.c ["w"]) = true) (hnt : k ≠ mTABLE) (hT : Tab f) (hS : stepS p σ = some σ')
    (hw' : World σ' p (L0 b.size om) f') : Tab f' :=
  tab_of_tkeep (by unfold L0; omega) hw hw' (stepS_tkeep hw hs (by unfold L0; omega) hm hk htk hS) (by rw [hm]; exact hnt) hT

/-- **(T) is kept by every DEFLATE step.** -/
theorem stepS_tab {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f)
    (hT : Tab f) (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2068 ≤ L0 b.size om := by unfold L0; omega
  have hv := hi.1.mode_ok
  simp only [validModes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h
  · -- TABLE
    have hm : f cMODE = mTABLE := h
    have hT' : BitsUpTo f (8 * f cTB + f cTI) := by unfold Tab at hT; rwa [if_pos hm] at hT
    obtain ⟨σ1, f1, hS1, hw1, -, hb1, -, hk⟩ := table_one hw hi hm hT'
    have e := Option.some.inj (hS1.symm.trans hS)
    subst e
    apply tab_congr hL hw1 hw'
    unfold Tab
    rcases hk with ⟨_, hm1, hc⟩ | ⟨hend, hm1⟩
    · rw [if_pos hm1, hc]; exact hb1
    · rw [if_neg (by rw [hm1]; decide), ← hend]; exact hb1
  · exact tab_tk hw hs h rfl tk_hdr (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_read (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_hdrb (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_hdrd (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_shdr (by decide) hT hS hw'
  · exact tab_fixlens hw hi h hT hS hw'
  · exact tab_tk hw hs h rfl tk_dhdr (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_slen (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_snlen (by decide) hT hS hw'
  · exact tab_scopy hw hi h hT hS hw'
  · exact tab_build hw hi h hT hS hw'
  · exact tab_lens hw hi h hT hS hw'
  · exact tab_sym hw hi h hT hS hw'
  · exact tab_decode hb hw hi h hT hS hw'
  · exact tab_symd hw hi h hT hS hw'
  · exact tab_lenx hw hi h hT hS hw'
  · exact tab_tk hw hs h rfl tk_dstd (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_dstx (by decide) hT hS hw'
  · exact tab_copy hw hi h hT hS hw'
  · exact tab_tk hw hs h rfl tk_dh2 (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_dh3 (by decide) hT hS hw'
  · exact tab_tk hw hs h rfl tk_dh4 (by decide) hT hS hw'
  · exact tab_clread hw hi h hT hS hw'
  · exact tab_clput hw hi h hT hS hw'
  · exact tab_lsym hw hi h hT hS hw'
  · exact tab_tk hw hs h rfl tk_lrep (by decide) hT hS hw'
  · exact tab_rep hw hi h hT hS hw'
  · have e := Option.some.inj ((stepS_fixed hw (by omega) (Or.inl h)).symm.trans hS)
    subst e
    exact tab_congr hL hw hw' hT
  · have e := Option.some.inj ((stepS_fixed hw (by omega) (Or.inr h)).symm.trans hS)
    subst e
    exact tab_congr hL hw hw' hT

/-- **(T) along the DEFLATE iterate.** -/
theorem iterS_tab (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (j : Nat) (σ σ' : Store) (f : Int → Int), World σ p (L0 b.size om) f → Sole σ p (L0 b.size om) →
      Inv b om lit f → Tab f → iterS p j σ = some σ' → ∀ f', World σ' p (L0 b.size om) f' → Tab f' := by
  intro j
  induction j with
  | zero =>
    intro σ σ' f hw _ _ hT h f' hw'
    simp only [iterS, Option.some.injEq] at h
    subst h
    exact tab_congr (by unfold L0; omega) hw hw' hT
  | succ j ih =>
    intro σ σ' f hw hs hi hT h f' hw'
    rcases h1 : stepS p σ with _ | σ1
    · simp [iterS, h1] at h
    · simp only [iterS, h1, Option.bind_some] at h
      obtain ⟨f1, hw1, hi1⟩ := reach_inv b om lit p hb 1 σ σ1 f hw hi (by simp [iterS, h1])
      exact ih σ1 σ' f1 hw1 (stepS_sole hs h1) hi1 (stepS_tab hb hw hs hi hT h1 hw1) h f' hw'

end VIRL5
