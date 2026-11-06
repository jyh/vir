/-
  O95 layer L4, Lean arm (amend-21 Q8, exploratory). Deadlock is OUTSIDE partial correctness (OBJECT-L4 §3): one deadlocking
  program D — a thread that acquires its own lock twice — satisfies `{emp} D {_. False}`, and its run reaches a BLOCKED
  configuration (no step, a wait on a held lock), never a fault. Stated so that no reader counts deadlock freedom as missing.
-/
import VIRL4.Programs

namespace VIRL4
open VIRL1 VIRL2

/-- D: `let c ← alloc(1) in let ℓ ← newlock(c) in let d₁ ← acquire(ℓ) in let d₂ ← acquire(ℓ) in ret d₂`. -/
def D : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp .newlock [v4 0] t4lock <|
  .letOp .acquire [v4 0] t4cap <|
  .letOp .acquire [v4 1] t4cap <|
  .ret (v4 0)

/-- Q8: `{emp} D {_. False}` under I₁. The second acquire's continuation would own the lock's region twice. -/
theorem D_triple_false : Triple₄ I₁ (fun _ σ => σ = Store.empty) D (fun _ _ _ => False) := by
  unfold D
  refine op₄_rule (vs := [c4 1]) (ws := [.const (.int 1)]) rfl rfl
    (Post := fun v _ σ => ∃ p, v = capv p ∧ RegionAt p 1 (fun _ => 0) σ) ?_ ?_
  · intro L σ h
    refine ⟨Assn.emp, _, alloc_axiom 1 (by decide), h, ?_⟩
    rintro v σq ⟨p, rfl, hq⟩
    exact ⟨p, rfl, hq⟩
  · intro v
    apply triple₄_pre_ex
    intro p
    apply triple₄_pre_pure
    rintro rfl
    show Triple₄ I₁ _ (.letOp .newlock [capv p] t4lock <| .letOp .acquire [v4 0] t4cap <|
      .letOp .acquire [v4 1] t4cap <| .ret (v4 0)) _
    refine newlock₄_rule (p := p) (P' := fun _ σ => σ = Store.empty) ?_ (fun _ _ _ _ h => h) (fun k => ?_)
    · rintro L σ hf
      exact release_split (l := 0) (L := L) hf
    · show Triple₄ I₁ _ (.letOp .acquire [lockv k] t4cap <| .letOp .acquire [lockv k] t4cap <| .ret (v4 0)) _
      refine acquire₄_rule (p := p) (fun L σ h => h.2) (stable_emp_LB k p) ?_
      show Triple₄ I₁ _ (.letOp .acquire [lockv k] t4cap <| .ret (v4 0)) _
      refine triple₄_conseq (P := fun L σ' => OwnsRegion p σ' ∧ LB k p L) ?_
        (acquire₄_rule (p := p) (fun L σ h => h.2) (fun _ _ _ hx h => ⟨h.1, base_of_ext h.2 hx⟩) ?_)
      · rintro L σ' ⟨σ, σI, _, rfl, ⟨rfl, hb⟩, ho, _⟩
        rw [Store.empty_union]
        exact ⟨ho, hb⟩
      · intro n L σ hpre
        obtain ⟨σa, σb, hd, _, ⟨hoa, _⟩, hob, _⟩ := hpre
        exact (hd.2 p (owns_mem hoa) (owns_mem hob)).elim

/-- D's run: three ⟶₄ steps reach a configuration that is BLOCKED (no step; it waits on lock 0, which it holds itself). -/
theorem D_blocks : ∃ c, Steps₄ (D, ⟨Store.empty ⊎ Store.empty ⊎ Store.empty, []⟩) c ∧ Blocked₄ c := by
  refine ⟨_, .step (.op rfl rfl) (.step (.op rfl rfl) (.step (.op rfl rfl) (.refl _))), ?_, Waits.acq rfl⟩
  intro c' hs
  cases hs with
  | op h1 h2 =>
    have : Atom₄.evalL [lockv 0] = some [lockv 0] := rfl
    change Atom₄.evalL [lockv 0] = _ at h1
    rw [this] at h1
    cases h1
    simp [opStep₄, lockv] at h2

end VIRL4
