/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅'s LIFTED and TERMINAL cases. `stepT₅` and
  `ιE stepT` differ only in branches the run does not take, so on a mode whose entry is DEFLATE's own (or that has no entry)
  their runs agree at any fuel ≥ 29. `run₅_ι` then carries DEFLATE's `stepS p σ = some σ'` to `stepS₅ p σ = some σ'`.
-/
import VIRL5.Outer5
import VIRDeflate.Fit

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- One step at a mode test. -/
theorem run₅_ite_eq (N : Nat) (m k : Int) (e₁ e₂ : Tm₅) (σ : Store) :
    run₅ (N + 1) (.ite (.prim .eq [.const (.int m), .const (.int k)]) e₁ e₂, σ) = run₅ N (if m = k then e₁ else e₂, σ) := by
  by_cases h : m = k
  · simp [run₅, stepFn₅, Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, Const.toBool, h]
  · simp [run₅, stepFn₅, Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, Const.toBool, h]

/-- The dispatch at the mode value m, closed at ⟨p⟩. -/
abbrev dispAt (p m : Int) (A : List (Int × Tm₅)) : Tm₅ :=
  ((disp₅ A).subst 1 (.const (.cap p))).subst 0 (.const (.int m))

/-- Two dispatches with the same keys and the same entry at m run alike at any fuel ≥ their length. -/
theorem disp₅_agree (p m : Int) (σ : Store) : ∀ (A B : List (Int × Tm₅)), A.map Prod.fst = B.map Prod.fst →
    A.lookup m = B.lookup m → ∀ N, A.length ≤ N → run₅ N (dispAt p m A, σ) = run₅ N (dispAt p m B, σ)
  | [], [], _, _, N, _ => rfl
  | [], _ :: _, hk, _, _, _ => by simp at hk
  | _ :: _, [], hk, _, _, _ => by simp at hk
  | (k, a) :: A, (k', b) :: B, hk, hl, N, hN => by
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨hkk, hk⟩ := hk
    subst hkk
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    have e : ∀ (t : Tm₅) (R : List (Int × Tm₅)), dispAt p m ((k, t) :: R) =
        .ite (.prim .eq [.const (.int m), .const (.int k)]) ((t.subst 1 (.const (.cap p))).subst 0 (.const (.int m)))
          (dispAt p m R) := by
      intro t R; simp [dispAt, disp₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    rw [e, e, run₅_ite_eq, run₅_ite_eq]
    by_cases hm : m = k
    · subst hm
      have hab : a = b := by simpa [List.lookup] using hl
      subst hab
      simp
    · have hb : (m == k) = false := by simp [hm]
      have hl' : A.lookup m = B.lookup m := by simpa [List.lookup, hb] using hl
      simp only [hm, if_false]
      exact disp₅_agree p m σ A B hk hl' N' (by simp at hN; omega)

/-- DEFLATE's dispatch, lifted, is `disp₅` of its lifted entries. -/
theorem lift_dispN : ∀ (ms : List (Int × NT)),
    ιE ((dispN ms).c ["md", "w"]) = disp₅ (ms.map fun kt => (kt.1, lift₅ kt.2))
  | [] => by simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, ιE, ιA, disp₅]
  | (k, t) :: r => by
    have ih := lift_dispN r
    simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, ιE, ιA, ιL, disp₅, lift₅, ih]

/-- The lifted entries of `modes`. -/
def modesL : List (Int × Tm₅) := modes.map fun kt => (kt.1, lift₅ kt.2)

theorem modes₅_keys : modes₅.map Prod.fst = modesL.map Prod.fst := by
  simp [modes₅, modesL, modes]

theorem modes₅_length : modes₅.length = 28 := rfl

/-- DEFLATE's step term, lifted. -/
theorem lift_stepT : ιE stepT = .letOp .load [.var 0, .const (.int cMODE)] t5int (disp₅ modesL) := by
  simp [stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, ιE, ιL, ιA, ιT, tint, t5int, lift_dispN, modesL]

/-- The first ⟶₅ step: MODE loaded from the world. -/
theorem run₅_load_mode (N : Nat) {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L)
    (X : Tm₅) :
    run₅ (N + 1) (.letOp .load [.const (.cap p), .const (.int cMODE)] t5int X, σ) = run₅ N (X.subst 0 (.const (.int (f cMODE))), σ) := by
  have g0 := hw.cell 0 (le_refl _) (by omega)
  have hL' : (0 : Int) < (L : Int) := by omega
  simp [run₅, stepFn₅, Atom₅.evalL, Atom₅.eval, opStep₅, lowerV, opStep, Store.load, hw.reg, cMODE, ιA, hL, hL', g0]

/-- **The lifted and terminal cases:** on a mode whose entry is DEFLATE's own (or that has none), a DEFLATE step that returns
  the world is the ⟶₅ step. -/
theorem stepS₅_of_stepS {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L)
    (hm : modes₅.lookup (f cMODE) = modesL.lookup (f cMODE)) (h : stepS p σ = some σ') : stepS₅ p σ = some σ' := by
  have hrun : run₅ KSTEP (stepT₅.subst 0 (.const (.cap p)), σ) = ιC (run₂ KSTEP (closeAt p stepT, σ)) := by
    rw [← run₅_ι]
    show run₅ KSTEP (stepT₅.subst 0 (.const (.cap p)), σ) = run₅ KSTEP (ιE (closeAt p stepT), σ)
    rw [closeAt, ιE_subst, lift_stepT]
    show run₅ (511 + 1) _ = run₅ (511 + 1) _
    simp only [stepT₅, Tm₅.subst, Atom₅.substL, Atom₅.subst, ιA]
    simp only [show (0 : Nat) < 0 + 1 by omega, if_true, show ¬ (0 < 0) by omega, if_false]
    rw [run₅_load_mode 511 hw hL, run₅_load_mode 511 hw hL]
    exact disp₅_agree p (f cMODE) σ modes₅ modesL modes₅_keys hm 511 (by rw [modes₅_length]; omega)
  unfold stepS at h
  unfold stepS₅
  rw [hrun]
  rcases hr : run₂ KSTEP (closeAt p stepT, σ) with ⟨e, σ''⟩
  rw [hr] at h
  cases e with
  | ret a =>
    cases a with
    | const c =>
      cases c with
      | cap q =>
        simp only at h
        split_ifs at h with hq
        · simp [ιC, ιE, ιA, capOf₅, Atom₅.eval, hq]; simpa using h
      | _ => simp at h
    | _ => simp at h
  | _ => simp at h

end VIRL5
