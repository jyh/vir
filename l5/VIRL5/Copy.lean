/-
  O95 layer L5, Lean arm (amend-24 LV7): `copyR : (int × int × int) →[2] unit`, (s, d, len), copies [s, s + len) of the FIRST lent
  region into [d, d + len) of the SECOND, and hands BOTH back. This is erratum L5-E1's case: under L2 a body holding two regions had
  no typed ending; here the body ends `retK unit [c_src, c_dst]` and the tail call lends both. Precondition: the two regions, their
  sizes, the index bounds; NO premise on either region's contents (LV7).
-/
import VIRL5.Fill
import VIRL2.Triples

namespace VIRL5
open VIRL1 VIRL2

theorem op_conseq {P P' : Assn} {o : Op} {vs : List Atom₂} {Q : Atom₂ → Assn} (hP : ∀ σ, P' σ → P σ)
    (h : OpTriple P o vs Q) : OpTriple P' o vs Q := fun σ σf hp => h σ σf (hP σ hp)

theorem sep_pure_left {φ : Prop} {P R : Assn} {σ} (h : ((fun σ => φ ∧ P σ) ∗ R) σ) : φ ∧ (P ∗ R) σ := by
  obtain ⟨σ₁, σ₂, hd, rfl, ⟨hφ, hP⟩, hR⟩ := h
  exact ⟨hφ, σ₁, σ₂, hd, rfl, hP, hR⟩

/-- The argument type (s, (d, len)). -/
def τcopy : Ty₅ := .prod t5int (.prod t5int t5int)

/-- The body, under c_dst = #0, c_src = #1 (the lent regions, c₁ = src at #(k−1)), x = #2, f = #3. -/
def copyBody : Tm₅ :=
  .ite (.prim .le [.snd (.snd (.var 2)), .const (.int 0)])
    (.retK (.const .unit) [.var 1, .var 0])
    (.letOp .load [.var 1, .fst (.var 2)] t5int
      (.letOp .store [.var 1, .fst (.snd (.var 3)), .var 0] t5cap
        (.appK (.var 5)
          (.pair (.prim .add [.fst (.var 4), .const (.int 1)])
            (.pair (.prim .add [.fst (.snd (.var 4)), .const (.int 1)]) (.prim .sub [.snd (.snd (.var 4)), .const (.int 1)])))
          [.var 3, .var 0])))

def copyR : Atom₅ := .fix τcopy 2 t5unit copyBody

/-- What `copyR` leaves in the destination: [pd + d, pd + d + len) holds the source's [ps + s, …). -/
def copyF (f g : Int → Int) (ps s pd d : Int) (len : Nat) : Int → Int :=
  fun a => if pd + d ≤ a ∧ a < pd + d + len then f (ps + s + (a - (pd + d))) else g a

def copyArg (s d : Int) (len : Nat) : Atom₅ := .pair (.const (.int s)) (.pair (.const (.int d)) (.const (.int len)))

theorem copyF_zero (f g : Int → Int) (ps s pd d : Int) : copyF f g ps s pd d 0 = g := by
  funext a; unfold copyF; split_ifs <;> first | rfl | omega

theorem copyF_succ (f g : Int → Int) (ps s pd d : Int) (m : Nat) :
    copyF f (Function.update g (pd + d) (f (ps + s))) ps (s + 1) pd (d + 1) m = copyF f g ps s pd d (m + 1) := by
  funext a; unfold copyF
  by_cases ha : a = pd + d
  · subst ha; simp
  · rw [Function.update_of_ne ha]; push_cast
    split_ifs with h₁ h₂ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl

/-- **copyR's triple**: lent ⟨ps⟩ (contents f, size ns) and ⟨pd⟩ (contents g, size nd), with the index bounds, it hands both back,
  the source unchanged, the destination `copyF f g ps s pd d len`; no premise on f or g. -/
theorem copyR_spec (ps pd : Int) (ns nd : Nat) (f : Int → Int) : ∀ (len : Nat) (s d : Int) (g : Int → Int),
    0 ≤ s → s + len ≤ ns → 0 ≤ d → d + len ≤ nd →
    Triple₅ (RegionAt ps ns f ∗ RegionAt pd nd g) (.appK copyR (copyArg s d len) [.const (.cap ps), .const (.cap pd)])
      (fun r qs σ => r = .const .unit ∧ qs = [.const (.cap ps), .const (.cap pd)] ∧
        (RegionAt ps ns f ∗ RegionAt pd nd (copyF f g ps s pd d len)) σ)
  | 0, s, d, g, hs, hsn, hd, hdn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, copyBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap ps), .const (.cap pd)] ∧
          (RegionAt ps ns f ∗ RegionAt pd nd g) σ) rfl rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      exact ⟨rfl, rfl, by rw [copyF_zero]; exact hσ⟩
  | m + 1, s, d, g, hs, hsn, hd, hdn => by
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, copyBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      simp only [Bool.false_eq_true, if_false]
      -- load the source cell
      refine letOp_rule₅ (cs := [.cap ps, .int s]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (op_frame (RegionAt pd nd g) (load_at ps ns f s ⟨hs, by push_cast at hsn; omega⟩)) (fun w => ?_)
      refine conseq₅ (fun σ h => sep_pure_left h) (fun r qs σ h => h) ?_
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      -- store it into the destination (the source region framed)
      refine letOp_rule₅ (cs := [.cap pd, .int d, .int (f (ps + s))]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (op_conseq (fun σ h => sep_comm h)
          (op_frame (RegionAt ps ns f) (store_at pd nd g d (f (ps + s)) ⟨hd, by push_cast at hdn; omega⟩)))
        (fun c => ?_)
      refine conseq₅ (fun σ h => ?_) (fun r qs σ h => h)
        (pre_pure₅ (φ := c = .const (.cap pd))
          (P := RegionAt ps ns f ∗ RegionAt pd nd (Function.update g (pd + d) (f (ps + s)))) (fun hc => ?_))
      · obtain ⟨hφ, h'⟩ := sep_pure_left h; exact ⟨hφ, sep_comm h'⟩
      subst hc
      have ih := copyR_spec ps pd ns nd f m (s + 1) (d + 1) (Function.update g (pd + d) (f (ps + s))) (by omega)
        (by push_cast at hsn ⊢; omega) (by omega) (by push_cast at hdn ⊢; omega)
      rw [copyF_succ] at ih
      have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine appKFix_rule₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]

end VIRL5
