/-
  O95 layer L5, Lean arm (amend-24 LV7): `cmpR : (int × int × int) →[2] bool`, (a, b, len), compares [a, a + len) of the first lent
  region with [b, b + len) of the second, cell by cell, and hands both back unchanged. The result is the decision of the pointwise
  equality. Precondition: the two regions, their sizes, the index bounds; NO premise on the contents (LV7).
-/
import VIRL5.Copy

namespace VIRL5
open VIRL1 VIRL2

/-- The body, under c_b = #0, c_a = #1, x = #2, f = #3. -/
def cmpBody : Tm₅ :=
  .ite (.prim .le [.snd (.snd (.var 2)), .const (.int 0)])
    (.retK (.const (.bool true)) [.var 1, .var 0])
    (.letOp .load [.var 1, .fst (.var 2)] t5int
      (.letOp .load [.var 1, .fst (.snd (.var 3))] t5int
        (.ite (.prim .eq [.var 1, .var 0])
          (.appK (.var 5)
            (.pair (.prim .add [.fst (.var 4), .const (.int 1)])
              (.pair (.prim .add [.fst (.snd (.var 4)), .const (.int 1)]) (.prim .sub [.snd (.snd (.var 4)), .const (.int 1)])))
            [.var 3, .var 2])
          (.retK (.const (.bool false)) [.var 3, .var 2]))))

def cmpR : Atom₅ := .fix τcopy 2 t5bool cmpBody

/-- The pointwise equality cmpR decides. -/
def CmpP (f g : Int → Int) (pa a pb b : Int) (len : Nat) : Prop := ∀ i : Nat, i < len → f (pa + a + i) = g (pb + b + i)

instance (f g : Int → Int) (pa a pb b : Int) (len : Nat) : Decidable (CmpP f g pa a pb b len) :=
  inferInstanceAs (Decidable (∀ i : Nat, i < len → f (pa + a + i) = g (pb + b + i)))

theorem cmpP_zero (f g : Int → Int) (pa a pb b : Int) : CmpP f g pa a pb b 0 := fun i hi => absurd hi (Nat.not_lt_zero _)

theorem cmpP_succ (f g : Int → Int) (pa a pb b : Int) (m : Nat) :
    CmpP f g pa a pb b (m + 1) ↔ f (pa + a) = g (pb + b) ∧ CmpP f g pa (a + 1) pb (b + 1) m := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
    have := h (i + 1) (by omega); push_cast at this ⊢
    rw [show pa + (a + 1) + i = pa + a + (i + 1) by omega, show pb + (b + 1) + i = pb + b + (i + 1) by omega]; exact this
  · rintro ⟨h₀, h⟩ i hi
    rcases i with _ | i
    · simpa using h₀
    · have := h i (by omega); push_cast at this ⊢
      rw [show pa + a + (i + 1) = pa + (a + 1) + i by omega, show pb + b + (i + 1) = pb + (b + 1) + i by omega]; exact this

/-- **cmpR's triple**: both regions handed back unchanged, the result `decide (CmpP …)`; no premise on f or g. -/
theorem cmpR_spec (pa pb : Int) (na nb : Nat) (f g : Int → Int) : ∀ (len : Nat) (a b : Int),
    0 ≤ a → a + len ≤ na → 0 ≤ b → b + len ≤ nb →
    Triple₅ (RegionAt pa na f ∗ RegionAt pb nb g) (.appK cmpR (copyArg a b len) [.const (.cap pa), .const (.cap pb)])
      (fun r qs σ => r = .const (.bool (decide (CmpP f g pa a pb b len))) ∧ qs = [.const (.cap pa), .const (.cap pb)] ∧
        (RegionAt pa na f ∗ RegionAt pb nb g) σ)
  | 0, a, b, ha, han, hb, hbn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cmpBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .const (.bool true) ∧ qs = [.const (.cap pa), .const (.cap pb)] ∧
          (RegionAt pa na f ∗ RegionAt pb nb g) σ) rfl rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      exact ⟨by simp [cmpP_zero], rfl, hσ⟩
  | m + 1, a, b, ha, han, hb, hbn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cmpBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      simp only [Bool.false_eq_true, if_false]
      refine letOp_rule₅ (cs := [.cap pa, .int a]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (op_frame (RegionAt pb nb g) (load_at pa na f a ⟨ha, by push_cast at han; omega⟩)) (fun w₁ => ?_)
      refine conseq₅ (fun σ h => sep_pure_left h) (fun r qs σ h => h) ?_
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap pb, .int b]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (op_conseq (fun σ h => sep_comm h) (op_frame (RegionAt pa na f) (load_at pb nb g b ⟨hb, by push_cast at hbn; omega⟩)))
        (fun w₂ => ?_)
      refine conseq₅ (fun σ h => ?_) (fun r qs σ h => h)
        (pre_pure₅ (φ := w₂ = .const (.int (g (pb + b)))) (P := RegionAt pa na f ∗ RegionAt pb nb g) (fun hw => ?_))
      · obtain ⟨hφ, h'⟩ := sep_pure_left h; exact ⟨hφ, sep_comm h'⟩
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      by_cases heq : f (pa + a) = g (pb + b)
      · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1, Atom₅.subst, heq]) ?_
        simp only [if_true]
        have ih := cmpR_spec pa pb na nb f g m (a + 1) (b + 1) (by omega) (by push_cast at han ⊢; omega) (by omega)
          (by push_cast at hbn ⊢; omega)
        have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
        refine conseq₅ (fun σ h => h) (fun r qs σ h => ?_) (appKFix_rule₅ rfl ?_ rfl rfl ih')
        · obtain ⟨rfl, rfl, hσ⟩ := h
          refine ⟨?_, rfl, hσ⟩
          congr 2; exact decide_eq_decide.mpr (by rw [cmpP_succ]; exact ⟨fun h => ⟨heq, h⟩, fun h => h.2⟩)
        all_goals simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]
      · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1, Atom₅.subst, heq]) ?_
        simp only [Bool.false_eq_true, if_false]
        refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
          (retK_rule₅ (Q := fun r qs σ => r = .const (.bool false) ∧ qs = [.const (.cap pa), .const (.cap pb)] ∧
            (RegionAt pa na f ∗ RegionAt pb nb g) σ) rfl rfl)
        obtain ⟨rfl, rfl, hσ⟩ := h
        refine ⟨?_, rfl, hσ⟩
        have : ¬ CmpP f g pa a pb b (m + 1) := fun h => heq ((cmpP_succ f g pa a pb b m).1 h).1
        simp [this]

end VIRL5
