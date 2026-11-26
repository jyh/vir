/-
  O95, OBJECT-NOCHECK-ENTRY (amend-27, NE3), route file 2: a word program with no `store` in its main code or its table never changes
  word memory. The decider's read-only predicate, and the fact the entry stub's FAULT outcome reads. A new file (NE4).
-/
import VIRC.Word

namespace S3
open VIRC

/-- No `store` anywhere in a word code. -/
def storeFree : WCode → Bool
  | .ret _ => true
  | .letE c₁ c₂ => storeFree c₁ && storeFree c₂
  | .load _ _ k => storeFree k
  | .store _ _ _ _ => false
  | .app _ _ => true
  | .ite _ c₁ c₂ => storeFree c₁ && storeFree c₂
  | .case _ _ _ c₁ c₂ => storeFree c₁ && storeFree c₂

/-- The decider's predicate (OBJECT-NOCHECK-ENTRY NE-D): main and every table body are store-free. -/
def ReadOnlyW (tbl : Table) (main : WCode) : Bool := storeFree main && tbl.all fun e => storeFree e.2

/-- The invariant: the code being run and every pending continuation are store-free. -/
def SFState : WSt → Prop
  | .run c _ k => storeFree c = true ∧ ∀ q ∈ k, storeFree q.1 = true
  | _ => True

theorem sf_step {tbl : Table} (ht : ∀ e ∈ tbl, storeFree e.2 = true) {s s' : WSt × WMem} (hs : SFState s.1)
    (h : stepW tbl s = some s') : SFState s'.1 ∧ s'.2 = s.2 := by
  obtain ⟨w, m⟩ := s
  cases w with
  | done _ => simp [stepW] at h
  | fault => simp [stepW] at h
  | ovf => simp [stepW] at h
  | run c ρ k =>
    obtain ⟨hc, hk⟩ := hs
    cases c with
    | ret o =>
      simp only [stepW] at h
      split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;> (try simp at h)
      all_goals first
        | exact ⟨trivial, rfl⟩
        | exact ⟨⟨hk _ (List.mem_cons_self ..), fun q hq => hk q (List.mem_cons_of_mem _ hq)⟩, rfl⟩
    | letE c₁ c₂ =>
      simp only [storeFree, Bool.and_eq_true] at hc
      simp only [stepW, Option.some.injEq] at h; subst h
      refine ⟨⟨hc.1, ?_⟩, rfl⟩
      intro q hq; rcases List.mem_cons.mp hq with rfl | hq
      · exact hc.2
      · exact hk q hq
    | load off idx c =>
      simp only [storeFree] at hc
      simp only [stepW] at h
      split at h <;> (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> (try subst h) <;>
        first | exact ⟨trivial, rfl⟩ | exact ⟨⟨hc, hk⟩, rfl⟩ | simp at h
    | store off idx v c => simp [storeFree] at hc
    | app f x =>
      simp only [stepW] at h
      split at h <;> (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> (try subst h) <;>
        first | exact ⟨trivial, rfl⟩ | simp at h |
          exact ⟨⟨ht _ (List.mem_of_getElem? (by assumption)), hk⟩, rfl⟩
    | ite o c₁ c₂ =>
      simp only [storeFree, Bool.and_eq_true] at hc
      simp only [stepW] at h
      split at h <;> (try split at h) <;> (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
        (try subst h) <;> first | exact ⟨trivial, rfl⟩ | exact ⟨⟨hc.1, hk⟩, rfl⟩ | exact ⟨⟨hc.2, hk⟩, rfl⟩ | simp at h
    | case o n₁ n₂ c₁ c₂ =>
      simp only [storeFree, Bool.and_eq_true] at hc
      simp only [stepW] at h
      split at h <;> (try split at h) <;> (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
        (try subst h) <;> first | exact ⟨trivial, rfl⟩ | exact ⟨⟨hc.1, hk⟩, rfl⟩ | exact ⟨⟨hc.2, hk⟩, rfl⟩ | simp at h

/-- **readOnly_mem.** A run of a read-only word program never changes word memory. -/
theorem readOnly_mem {tbl : Table} {main : WCode} (hro : ReadOnlyW tbl main = true) {ρ : List W} {m : WMem} :
    ∀ {n W'}, WN tbl n (.run main ρ [], m) W' → W'.2 = m := by
  simp only [ReadOnlyW, Bool.and_eq_true, List.all_eq_true] at hro
  have gen : ∀ {n s W'}, WN tbl n s W' → SFState s.1 → W'.2 = s.2 := by
    intro n s W' h
    induction h with
    | refl => intro _; rfl
    | step hs _ ih =>
      intro hsf
      obtain ⟨h1, h2⟩ := sf_step hro.2 hsf hs
      rw [ih h1, h2]
  intro n W' h
  exact gen h ⟨hro.1, by simp⟩

end S3
