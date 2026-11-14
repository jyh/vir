/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): the ⟶₅ side of Refine₅ for a RE-EXPRESSED mode. The
  dispatch reaches the mode's branch in k ≤ 28 steps (`disp₅_reach`), the branch is the mode's own term at ⟨p⟩ (`shift_branch₅`),
  and the mode's run lemma at every fuel ≥ its cost (each ≤ 483 = KSTEP − 29) makes it the step (`stepS₅_reex`).
-/
import VIRL5.Dispatch5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The dispatch reaches the entry for m in at most `ms.length` steps. -/
theorem disp₅_reach (p m : Int) (σ : Store) : ∀ (ms : List (Int × Tm₅)) (t : Tm₅), ms.lookup m = some t →
    ∃ k, k ≤ ms.length ∧ ∀ N, run₅ (k + N) (dispAt p m ms, σ) =
      run₅ N ((t.subst 1 (.const (.cap p))).subst 0 (.const (.int m)), σ)
  | [], t, h => by simp at h
  | (k', a) :: r, t, h => by
    have e : dispAt p m ((k', a) :: r) =
        .ite (.prim .eq [.const (.int m), .const (.int k')]) ((a.subst 1 (.const (.cap p))).subst 0 (.const (.int m)))
          (dispAt p m r) := by
      simp [dispAt, disp₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    by_cases hm : m = k'
    · subst hm
      have hat : a = t := by simpa [List.lookup] using h
      subst hat
      refine ⟨1, by simp, fun N => ?_⟩
      rw [e, show 1 + N = N + 1 by omega, run₅_ite_eq]
      simp
    · have hb : (m == k') = false := by simp [hm]
      have h' : r.lookup m = some t := by simpa [List.lookup, hb] using h
      obtain ⟨k, hk, hrun⟩ := disp₅_reach p m σ r t h'
      refine ⟨k + 1, by simp; omega, fun N => ?_⟩
      rw [e, show k + 1 + N = (k + N) + 1 by omega, run₅_ite_eq]
      simp only [hm, if_false]
      exact hrun N

/-- **A re-expressed mode's step:** if the mode's term, from σ, returns the world at every fuel from F₀ ≤ 483 with a store
  satisfying P, then `stepS₅ p σ` is such a store. -/
theorem stepS₅_reex {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) {t : Tm₅}
    (hm : modes₅.lookup (f cMODE) = some (t.shift 0)) {F₀ : Nat} (hF₀ : F₀ ≤ 483) {P : Store → Prop}
    (hrun : ∀ F, F₀ ≤ F → ∃ a, ((run₅ F (t.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
        (run₅ F (t.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
        P (run₅ F (t.subst 0 (.const (.cap p)), σ)).2) :
    ∃ σ', stepS₅ p σ = some σ' ∧ P σ' := by
  obtain ⟨k, hk, hd⟩ := disp₅_reach p (f cMODE) σ modes₅ (t.shift 0) hm
  rw [modes₅_length] at hk
  have hrun₅ : run₅ KSTEP (stepT₅.subst 0 (.const (.cap p)), σ) = run₅ (511 - k) (t.subst 0 (.const (.cap p)), σ) := by
    show run₅ (511 + 1) _ = _
    simp only [stepT₅, Tm₅.subst, Atom₅.substL, Atom₅.subst, ιA]
    simp only [show (0 : Nat) < 0 + 1 by omega, if_true, show ¬ (0 < 0) by omega, if_false]
    rw [run₅_load_mode 511 hw hL]
    have h1 := hd (511 - k)
    rw [show k + (511 - k) = 511 by omega, branch_shift₅] at h1
    exact h1
  obtain ⟨a, hterm, hav, hP⟩ := hrun (511 - k) (by omega)
  refine ⟨(run₅ (511 - k) (t.subst 0 (.const (.cap p)), σ)).2, ?_, hP⟩
  unfold stepS₅
  rw [hrun₅]
  rcases hterm with h | h <;> rw [h] <;> simp [capOf₅, hav]

end VIRL5
