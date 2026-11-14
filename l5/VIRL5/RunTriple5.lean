/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5). A triple is partial (no fault, and Q at every terminal reached); the COST
  clause `Cost₅ P e n` says run₅ n is terminal. Together, with the empty frame, they fix what `run₅ m` RETURNS for every m ≥ n:
  a terminal configuration whose store and value satisfy Q. This is how a mode's triple becomes a fact about DEFLATE's
  `stepS`-shaped run at the constant fuel KSTEP.
-/
import VIRL5.Cost5

namespace VIRL5
open VIRL1 VIRL2

theorem union_empty' (σ : Store) : σ ⊎ Store.empty = σ := by
  simp [Store.empty, Store.union, Finmap.union_empty]

theorem disj_empty_right (σ : Store) : Store.Disj σ Store.empty :=
  ⟨fun x _ h => by first | exact Finmap.notMem_empty h | exact Finmap.not_mem_empty h | simp [Finmap.mem_def] at h,
   fun x _ h => by first | exact Finmap.notMem_empty h | exact Finmap.not_mem_empty h | simp [Finmap.mem_def] at h⟩

/-- **Triple + cost ⇒ the run's result.** -/
theorem run_of_triple₅ {P : Assn} {e : Tm₅} {Q : Atom₅ → List Atom₅ → Assn} {n : Nat}
    (ht : Triple₅ P e Q) (hc : Cost₅ P e n) {σ : Store} (hP : P σ) (hwf : Store.WF σ) {m : Nat} (hm : n ≤ m) :
    ∃ v qs, Q v qs (run₅ m (e, σ)).2 ∧
      ((∃ a, (run₅ m (e, σ)).1 = .ret a ∧ a.eval = some v ∧ qs = []) ∨
       (∃ a ds, (run₅ m (e, σ)).1 = .retK a ds ∧ a.eval = some v ∧ Atom₅.evalL ds = some qs)) := by
  have hd := disj_empty_right σ
  have hw : Store.WF (σ ⊎ Store.empty) := by rw [union_empty']; exact hwf
  have hT := (hc.mono hm) σ Store.empty hP hd hw
  obtain ⟨_, hret, hretK⟩ := ht σ Store.empty hP hd hw
  rw [union_empty'] at hT hret hretK
  have hs : Steps₅ (e, σ) (run₅ m (e, σ)) := run₅_steps m _
  generalize run₅ m (e, σ) = c at hT hs ⊢
  obtain ⟨t, σ'⟩ := c
  cases t <;> simp only [Tm₅.IsTerminal] at hT
  · rename_i a
    obtain ⟨v, σq, hv, -, hσ, -, hQ⟩ := hret a σ' hs
    rw [union_empty'] at hσ
    subst hσ
    exact ⟨v, [], hQ, Or.inl ⟨a, rfl, hv, rfl⟩⟩
  · rename_i a ds
    obtain ⟨v, qs, σq, hv, hqs, -, hσ, -, hQ⟩ := hretK a ds σ' hs
    rw [union_empty'] at hσ
    subst hσ
    exact ⟨v, qs, hQ, Or.inr ⟨a, ds, rfl, hv, hqs⟩⟩

end VIRL5
