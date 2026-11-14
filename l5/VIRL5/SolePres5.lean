/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5, owed item (ii)): a DEFLATE step keeps a store Sole. The
  step term only loads and stores (`opFree`: no alloc, no free, checked inside function bodies too, because TABLE applies one).
  ⟶₂ keeps `opFree` (substitution and evaluation keep it), a load leaves the store unchanged, and a store is bounds-checked
  against the region, so it writes a cell of the one region and R is unchanged. Hence `run₂` and `stepS` keep Sole.
-/
import VIRL5.Bridge5
import VIRDeflate.Dispatch

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The ops a Sole store survives. -/
def okOp : Op → Bool
  | .load => true
  | .store => true
  | _ => false

mutual
def opFreeA : Atom₂ → Bool
  | .var _ => true
  | .const _ => true
  | .prim _ as => opFreeL as
  | .lam _ e => opFree e
  | .fix _ _ e => opFree e
  | .pair a₁ a₂ => opFreeA a₁ && opFreeA a₂
  | .fst a => opFreeA a
  | .snd a => opFreeA a
  | .inl _ a => opFreeA a
  | .inr _ a => opFreeA a
def opFreeL : List Atom₂ → Bool
  | [] => true
  | a :: as => opFreeA a && opFreeL as
def opFree : Tm₂ → Bool
  | .ret a => opFreeA a
  | .letE _ e₁ e₂ => opFree e₁ && opFree e₂
  | .letOp o as _ e => okOp o && opFreeL as && opFree e
  | .app a₁ a₂ => opFreeA a₁ && opFreeA a₂
  | .ite a e₁ e₂ => opFreeA a && opFree e₁ && opFree e₂
  | .case a e₁ e₂ => opFreeA a && opFree e₁ && opFree e₂
end

mutual
theorem opFreeA_subst : ∀ (a : Atom₂) (k : Nat) (v : Atom₂), opFreeA v = true → opFreeA a = true →
    opFreeA (a.subst k v) = true
  | .var n, k, v, hv, _ => by
    simp only [Atom.subst]
    split_ifs <;> simp [opFreeA, hv]
  | .const c, _, _, _, _ => by simp [Atom.subst, opFreeA]
  | .prim p as, k, v, hv, ha => by
    simp only [Atom.subst, opFreeA] at ha ⊢; exact opFreeL_subst as k v hv ha
  | .lam τ e, k, v, hv, ha => by
    simp only [Atom.subst, opFreeA] at ha ⊢; exact opFree_subst e (k + 1) v hv ha
  | .fix τ₁ τ₂ e, k, v, hv, ha => by
    simp only [Atom.subst, opFreeA] at ha ⊢; exact opFree_subst e (k + 2) v hv ha
  | .pair a₁ a₂, k, v, hv, ha => by
    simp only [Atom.subst, opFreeA, Bool.and_eq_true] at ha ⊢
    exact ⟨opFreeA_subst a₁ k v hv ha.1, opFreeA_subst a₂ k v hv ha.2⟩
  | .fst a, k, v, hv, ha => by simp only [Atom.subst, opFreeA] at ha ⊢; exact opFreeA_subst a k v hv ha
  | .snd a, k, v, hv, ha => by simp only [Atom.subst, opFreeA] at ha ⊢; exact opFreeA_subst a k v hv ha
  | .inl τ a, k, v, hv, ha => by simp only [Atom.subst, opFreeA] at ha ⊢; exact opFreeA_subst a k v hv ha
  | .inr τ a, k, v, hv, ha => by simp only [Atom.subst, opFreeA] at ha ⊢; exact opFreeA_subst a k v hv ha
theorem opFreeL_subst : ∀ (as : List Atom₂) (k : Nat) (v : Atom₂), opFreeA v = true → opFreeL as = true →
    opFreeL (Atom.substL k v as) = true
  | [], _, _, _, _ => by simp [Atom.substL, opFreeL]
  | a :: as, k, v, hv, ha => by
    simp only [Atom.substL, opFreeL, Bool.and_eq_true] at ha ⊢
    exact ⟨opFreeA_subst a k v hv ha.1, opFreeL_subst as k v hv ha.2⟩
theorem opFree_subst : ∀ (e : Tm₂) (k : Nat) (v : Atom₂), opFreeA v = true → opFree e = true →
    opFree (e.subst k v) = true
  | .ret a, k, v, hv, he => by simp only [Tm.subst, opFree] at he ⊢; exact opFreeA_subst a k v hv he
  | .letE τ e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, opFree, Bool.and_eq_true] at he ⊢
    exact ⟨opFree_subst e₁ k v hv he.1, opFree_subst e₂ (k + 1) v hv he.2⟩
  | .letOp o as τ e, k, v, hv, he => by
    simp only [Tm.subst, opFree, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, opFreeL_subst as k v hv he.1.2⟩, opFree_subst e (k + 1) v hv he.2⟩
  | .app a₁ a₂, k, v, hv, he => by
    simp only [Tm.subst, opFree, Bool.and_eq_true] at he ⊢
    exact ⟨opFreeA_subst a₁ k v hv he.1, opFreeA_subst a₂ k v hv he.2⟩
  | .ite a e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, opFree, Bool.and_eq_true] at he ⊢
    exact ⟨⟨opFreeA_subst a k v hv he.1.1, opFree_subst e₁ k v hv he.1.2⟩, opFree_subst e₂ k v hv he.2⟩
  | .case a e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, opFree, Bool.and_eq_true] at he ⊢
    exact ⟨⟨opFreeA_subst a k v hv he.1.1, opFree_subst e₁ (k + 1) v hv he.1.2⟩, opFree_subst e₂ (k + 1) v hv he.2⟩
end

mutual
theorem opFreeA_eval : ∀ (a v : Atom₂), Atom.eval a = some v → opFreeA a = true → opFreeA v = true
  | .var _, v, h, _ => by simp [Atom.eval] at h
  | .const c, v, h, _ => by simp [Atom.eval] at h; subst h; simp [opFreeA]
  | .prim p as, v, h, _ => by
    simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, c, _, rfl⟩ := h
    simp [opFreeA]
  | .lam τ e, v, h, ha => by simp [Atom.eval] at h; subst h; exact ha
  | .fix τ₁ τ₂ e, v, h, ha => by simp [Atom.eval] at h; subst h; exact ha
  | .pair a₁ a₂, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := h
    simp only [opFreeA, Bool.and_eq_true] at ha ⊢
    exact ⟨opFreeA_eval a₁ v₁ h₁ ha.1, opFreeA_eval a₂ v₂ h₂ ha.2⟩
  | .fst a, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    have := opFreeA_eval a w hw ha
    cases w <;> simp at hv
    subst hv
    simp only [opFreeA, Bool.and_eq_true] at this
    exact this.1
  | .snd a, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    have := opFreeA_eval a w hw ha
    cases w <;> simp at hv
    subst hv
    simp only [opFreeA, Bool.and_eq_true] at this
    exact this.2
  | .inl τ a, v, h, ha => by
    simp only [Atom.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp only [opFreeA] at ha ⊢
    exact opFreeA_eval a w hw ha
  | .inr τ a, v, h, ha => by
    simp only [Atom.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp only [opFreeA] at ha ⊢
    exact opFreeA_eval a w hw ha
end

/-- A pure ⟶ step keeps `opFree`. -/
theorem pure_opFree {e e' : Tm₂} (h : Step e e') : opFree e = true → opFree e' = true := by
  induction h with
  | @letRet τ a v e₂ hv =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf
    exact opFree_subst e₂ 0 v (opFreeA_eval a v hv hf.1) hf.2
  | @letStep τ e₁ e₁' e₂ _ ih =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf ⊢
    exact ⟨ih hf.1, hf.2⟩
  | @appLam a₁ a₂ τ e v h₁ h₂ =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf
    have hl := opFreeA_eval a₁ _ h₁ hf.1
    simp only [opFreeA] at hl
    exact opFree_subst e 0 v (opFreeA_eval a₂ v h₂ hf.2) hl
  | @appFix a₁ a₂ τ₁ τ₂ e v h₁ h₂ =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf
    have hl := opFreeA_eval a₁ _ h₁ hf.1
    have hl' := hl
    simp only [opFreeA] at hl
    exact opFree_subst _ 0 _ hl' (opFree_subst e 0 v (opFreeA_eval a₂ v h₂ hf.2) hl)
  | iteT =>
    intro hf; simp only [opFree, Bool.and_eq_true] at hf; exact hf.1.2
  | iteF =>
    intro hf; simp only [opFree, Bool.and_eq_true] at hf; exact hf.2
  | @caseL a e₁ e₂ τ v hv =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf
    have hi := opFreeA_eval a _ hv hf.1.1
    simp only [opFreeA] at hi
    exact opFree_subst e₁ 0 v hi hf.1.2
  | @caseR a e₁ e₂ τ v hv =>
    intro hf
    simp only [opFree, Bool.and_eq_true] at hf
    have hi := opFreeA_eval a _ hv hf.1.1
    simp only [opFreeA] at hi
    exact opFree_subst e₂ 0 v hi hf.2

/-- A load or a store keeps a store Sole, and returns a constant. -/
theorem opStep_sole {o : Op} {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} {p : Int} {L : Nat}
    (ho : okOp o = true) (h : opStep o vs σ = some (v, σ')) (hs : Sole σ p L) : Sole σ' p L ∧ opFreeA v = true := by
  cases o <;> simp only [okOp, Bool.false_eq_true] at ho
  · -- load
    unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, rfl⟩ := h
    exact ⟨hs, by simp [opFreeA]⟩
  · -- store
    unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    · rename_i q i w _
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨σ'', hst, rfl, rfl⟩ := h
      refine ⟨?_, by simp [opFreeA]⟩
      unfold Store.store at hst
      rw [hs.1] at hst
      by_cases hq : q = p
      · subst hq
        rw [Finmap.lookup_singleton_eq] at hst
        simp only at hst
        split_ifs at hst with hi
        simp only [Option.some.injEq] at hst
        subst hst
        refine ⟨rfl, fun a ha => ?_⟩
        have hne : a ≠ q + i := by
          intro e; apply ha; simp only [Store.InRegion]; omega
        simp only
        rw [Finmap.lookup_insert_of_ne _ hne]
        exact hs.2 a ha
      · have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := by
          rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact hq
        rw [this] at hst
        simp at hst

/-- A ⟶₂ step from an opFree term keeps the term opFree and the store Sole. -/
theorem step₂_sole {p : Int} {L : Nat} {c c' : Config} (h : Step₂ c c') :
    opFree c.1 = true → Sole c.2 p L → opFree c'.1 = true ∧ Sole c'.2 p L := by
  induction h with
  | pure hs => intro hf hσ; exact ⟨pure_opFree hs hf, hσ⟩
  | @letStep τ e₁ e₁' e₂ σ σ' _ ih =>
    intro hf hσ
    simp only [opFree, Bool.and_eq_true] at hf ⊢
    obtain ⟨h1, h2⟩ := ih hf.1 hσ
    exact ⟨⟨h1, hf.2⟩, h2⟩
  | @op o as τ e vs v σ σ' _ hop =>
    intro hf hσ
    simp only [opFree, Bool.and_eq_true] at hf
    obtain ⟨hs', hv⟩ := opStep_sole hf.1.1 hop hσ
    exact ⟨opFree_subst e 0 v hv hf.2, hs'⟩

/-- `run₂` from an opFree term keeps the store Sole. -/
theorem run₂_sole {p : Int} {L : Nat} : ∀ (n : Nat) (e : Tm₂) (σ : Store), opFree e = true → Sole σ p L →
    Sole (run₂ n (e, σ)).2 p L
  | 0, _, _, _, hs => hs
  | n + 1, e, σ, hf, hs => by
    simp only [run₂]
    rcases hfn : stepFn₂ e σ with _ | ⟨e', σ'⟩
    · exact hs
    · obtain ⟨hf', hs'⟩ := step₂_sole (stepFn₂_sound hfn) hf hs
      exact run₂_sole n e' σ' hf' hs'

/-- DEFLATE's step term only loads and stores. -/
theorem opFree_stepT : opFree stepT = true := by
  decide

/-- **Owed (ii): a DEFLATE step keeps the store Sole.** -/
theorem stepS_sole {p : Int} {L : Nat} {σ σ' : Store} (hs : Sole σ p L) (h : stepS p σ = some σ') : Sole σ' p L := by
  have hrun := run₂_sole KSTEP (closeAt p stepT) σ (opFree_subst stepT 0 _ (by simp [opFreeA]) opFree_stepT) hs
  unfold stepS at h
  rcases hr : run₂ KSTEP (closeAt p stepT, σ) with ⟨e, σ''⟩
  rw [hr] at h hrun
  cases e with
  | ret a =>
    cases a with
    | const c =>
      cases c with
      | cap q =>
        simp only at h
        split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact hrun
      | _ => simp at h
    | _ => simp at h
  | _ => simp at h

end VIRL5
