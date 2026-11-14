/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ at COPY, as at REP. The ⟶₅ step copies
  c = min(PEND, 32) bytes in one copyWithinR call, the forward copy `cwF` (overlap allowed, RFC 1951's order); DEFLATE copies
  one per step (copy_byte), so c DEFLATE steps reach the same contents (`copy_iter`, read through `cwR`, cwF relative to the
  base). At PEND = 0 both take DEFLATE's own end branch (MODE := SYM), j = 1.
-/
import VIRL5.RefineRep5
import VIRL5.CopyRun5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The forward copy, relative to the base. -/
def cwR : (Int → Int) → Int → Int → Nat → (Int → Int)
  | g, _, _, 0 => g
  | g, s, d, m + 1 => cwR (Function.update g d (g s)) (s + 1) (d + 1) m

/-- `cwF` at the base p is `cwR` read through it. -/
theorem cwF_rel (p : Int) : ∀ (c : Nat) (f : Int → Int) (s d i : Int),
    cwF p (fun a => f (a - p)) s d c (p + i) = cwR f s d c i
  | 0, f, s, d, i => by simp [cwF, cwR]
  | c + 1, f, s, d, i => by
    have e : Function.update (fun a => f (a - p)) (p + d) (f (p + s - p)) = fun a => (Function.update f d (f s)) (a - p) := by
      funext a
      by_cases h : a = p + d
      · subst h; simp
      · have h' : a - p ≠ d := by omega
        simp [Function.update_apply, h, h']
    simp only [cwF, cwR]
    rw [e]
    exact cwF_rel p c _ (s + 1) (d + 1) i

/-- A cell below both ranges is untouched by the copy, and its update commutes with it. -/
theorem cwR_update (k v : Int) : ∀ (c : Nat) (g : Int → Int) (s d : Int), k < s → k < d →
    cwR (Function.update g k v) s d c = Function.update (cwR g s d c) k v
  | 0, g, s, d, _, _ => rfl
  | c + 1, g, s, d, hs, hd => by
    simp only [cwR]
    rw [Function.update_apply, if_neg (by omega), Function.update_comm (by omega : k ≠ d)]
    exact cwR_update k v c _ (s + 1) (d + 1) (by omega) (by omega)

/-! ## COPY's end branch over ⟶₅ -/

theorem copy5_end_cost (p : Int) (L : Nat) (g : Int → Int) (hpd : g (p + cPEND) = 0) (hL : 6 ≤ L) :
    Cost₅ (RegionAt p L g) (copyT₅.subst 0 (.const (.cap p))) 3 := by
  simp [copyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hpd]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  simp only [if_true]
  refine cost_letOp₅ (cs := [.cap p, .int cMODE, .int mSYM]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L g cMODE mSYM ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem copy5_end_world (p : Int) (L : Nat) (f : Int → Int) (hpd : f cPEND = 0) (hL : 6 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 3 ≤ F) :
    ∃ a, ((run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (fun a => f (a - p)) (p + cMODE) mSYM (p + i)) ∧
      Sole (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  have hpd' : (fun a => f (a - p)) (p + cPEND) = 0 := by simpa using hpd
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (copy5_end p L _ hpd' hL) (copy5_end_cost p L _ hpd' hL) hR hwf hF
  subst hv
  subst hqs
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hw', hs'⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hw', hs'⟩

/-! ## COPY over DEFLATE, c steps -/

/-- DEFLATE's contents after c COPY steps, relative to the base. -/
def copyRel (f : Int → Int) (pd m ds n : Int) (c : Nat) : Int → Int :=
  Function.update (Function.update (cwR f (2080 + n + m - ds) (2080 + n + m) c) cM (m + c)) cPEND (pd - c)

theorem copy_mem : (mCOPY, copyN) ∈ modes := by simp [modes]

theorem copy_iter {p : Int} {L : Nat} (hL : 2080 ≤ L) (n ds : Int) : ∀ (c : Nat) (σ : Store) (g : Int → Int) (pd m : Int),
    World σ p L g → g cMODE = mCOPY → g cPEND = pd → g cN = n → g cM = m → g cDIST = ds →
    (c : Int) ≤ pd → 0 ≤ ds → ds ≤ m → 0 ≤ n → 2080 + n + m + c ≤ L →
    ∃ σ', iterS p c σ = some σ' ∧ World σ' p L (copyRel g pd m ds n c)
  | 0, σ, g, pd, m, hw, _, hpd, _, hm, _, _, _, _, _, _ =>
    ⟨σ, rfl, world_congr hw (fun i _ _ => by
      unfold copyRel
      simp only [cwR, Function.update_apply, Nat.cast_zero, add_zero, sub_zero]
      split_ifs with h1 h2 <;> (try subst_vars) <;> first | omega | simp_all)⟩
  | c + 1, σ, g, pd, m, hw, hmd, hpd, hn, hm, hds, hc, hd0, hdm, hn0, haL => by
    have hfit := modes_fit (mCOPY, copyN) copy_mem (by decide)
    have hS := stepS_of_mode hw (by omega) hmd rfl hfit.1 hfit.2
      (copy_byte hw hL pd n m ds (g (2080 + n + (m - ds))) hpd (by omega) hn hm hds (by omega) (by push_cast at haL; omega)
        rfl (by omega) (by push_cast at haL; omega))
    have hw1 := ((hw.store (i := 2080 + n + m) (v := g (2080 + n + (m - ds))) (by omega) (by push_cast at haL; omega)).store
      (i := 3) (v := m + 1) (by omega) (by omega)).store (i := 5) (v := pd - 1) (by omega) (by omega)
    set g1 := Function.update (Function.update (Function.update g (2080 + n + m) (g (2080 + n + (m - ds)))) 3 (m + 1)) 5
      (pd - 1) with hg1
    have u : ∀ d : Int, d ≠ 2080 + n + m → d ≠ 3 → d ≠ 5 → g1 d = g d := by
      intro d h1 h2 h3; simp [hg1, Function.update_apply, h1, h2, h3]
    obtain ⟨σ', hit, hw'⟩ := copy_iter hL n ds c _ g1 (pd - 1) (m + 1) hw1
      (by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hmd)
      (by simp [hg1, cPEND])
      (by rw [u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)]; exact hn)
      (by show g1 3 = m + 1; simp [hg1, Function.update_apply])
      (by rw [u _ (by unfold cDIST; omega) (by unfold cDIST; omega) (by unfold cDIST; omega)]; exact hds)
      (by push_cast at hc ⊢; omega) hd0 (by omega) hn0 (by push_cast at haL ⊢; omega)
    have e1 : cwR g1 (2080 + n + (m + 1) - ds) (2080 + n + (m + 1)) c =
        Function.update (Function.update (cwR g (2080 + n + m - ds) (2080 + n + m) (c + 1)) 3 (m + 1)) 5 (pd - 1) := by
      rw [hg1, cwR_update 5 _ c _ _ _ (by omega) (by omega), cwR_update 3 _ c _ _ _ (by omega) (by omega)]
      simp only [cwR]
      rw [show 2080 + n + (m + 1) - ds = 2080 + n + m - ds + 1 by ring, show 2080 + n + (m + 1) = 2080 + n + m + 1 by ring,
        show 2080 + n + (m - ds) = 2080 + n + m - ds by ring]
    refine ⟨σ', by simp only [iterS, hS, Option.bind_some]; exact hit, world_congr hw' (fun i _ _ => ?_)⟩
    unfold copyRel
    rw [e1]
    simp only [Function.update_apply, cPEND, cM]
    push_cast
    split_ifs <;> omega

/-! ## Refine₅ at COPY -/

theorem refine_copy (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f) (hm : f cMODE = mCOPY) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hwf := wf_of_sole hw hs (by omega)
  have hc := hi.2.cur
  rw [hm, facts_copy] at hc
  obtain ⟨-, -, hp0, hd0, hdm, hmo⟩ := hc
  have hn := hi.1.n_eq
  have hom := hi.1.om_eq
  have hlk : modes₅.lookup (f cMODE) = some (copyT₅.shift 0) := by rw [hm]; rfl
  have hfit := modes_fit (mCOPY, copyN) copy_mem (by decide)
  by_cases hpd : f cPEND = 0
  · obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 3) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (fun i => Function.update (fun a => f (a - p)) (p + cMODE) mSYM (p + i)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := copy5_end_world p (L0 b.size om) f hpd (by omega) hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (copy_end hw hL0 hpd)
    have hwD := hw.store (i := 0) (v := 13) (by omega) (by omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      simp [Function.update_apply, cMODE, mSYM])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · have hpd0 : 0 < f cPEND := by omega
    obtain ⟨c, hcd⟩ : ∃ c : Int, c = min (f cPEND) CS := ⟨_, rfl⟩
    have hc32 : c ≤ 32 := by rw [hcd]; unfold CS; omega
    have hcp : c ≤ f cPEND := by rw [hcd]; omega
    have hc0 : 0 < c := by rw [hcd]; unfold CS; omega
    have hcT : (c.toNat : Int) = c := Int.toNat_of_nonneg (by omega)
    have hbound' : 2080 + (b.size : Int) + f cM + c ≤ L0 b.size om := by unfold L0; omega
    have hbound : IN + (b.size : Int) + f cM + min (f cPEND) CS ≤ L0 b.size om := by
      rw [← hcd]; unfold IN; omega
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 4 * 32 + 12) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (copyPostRel p f (f cPEND) b.size (f cM) (f cDIST)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := copy5_chunk_world p (L0 b.size om) f (f cPEND) b.size (f cM) (f cDIST)
          rfl hpd0 hn rfl rfl (by omega) hd0 hdm hbound hw hs hwf (F := F) (by rw [← hcd]; omega)
        exact ⟨a, h1, h2, h3, h4⟩)
    obtain ⟨σD, hit, hwD⟩ := copy_iter hL0 b.size (f cDIST) c.toNat σ f (f cPEND) (f cM) hw hm rfl hn rfl rfl
      (by rw [hcT]; exact hcp) hd0 hdm (by omega) (by rw [hcT]; exact hbound')
    have hsD := iterS_sole _ σ σD hs hit
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      simp only [copyRel, copyPostRel, copyPost]
      simp only [← hcd]
      simp only [Function.update_apply, cwF_rel, hcT, cPEND, cM, IN, show p + i - p = i by omega,
        show (p + i = p + 3) = (i = 3) by simp, show (p + i = p + 5) = (i = 5) by simp]
      try (split_ifs <;> first | omega | rfl))
    subst e
    exact ⟨c.toNat, _, hstL, hit, hsL, fun _ _ => by omega⟩

end VIRL5
