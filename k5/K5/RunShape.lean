/-
  O95, row 298 (compiler/DECLARATIONS-K5.md Addendum 7), L-2. GENERIC over L2 programs: no DEFLATE constant.
  A ⟶₂ run whose term allocates nothing (`tmOk`: no alloc/free, every int literal in range) and whose primitive results stay in
  range (`SrcInRange`) keeps the store's regions, its WF, and every cell in range.
-/
import K5.Loader
import VIRL2.Axioms

namespace K5
open VIRL1 VIRL2 VIRC

mutual
/-- No alloc/free, and every int literal in range (λ/fix bodies included). -/
def atomOk : Atom₂ → Bool
  | .var _ => true
  | .const c => match c with
    | .int n => inRange n
    | _ => true
  | .prim _ as => atomOkL as
  | .lam _ e => tmOk e
  | .fix _ _ e => tmOk e
  | .pair a₁ a₂ => atomOk a₁ && atomOk a₂
  | .fst a => atomOk a
  | .snd a => atomOk a
  | .inl _ a => atomOk a
  | .inr _ a => atomOk a
def atomOkL : List Atom₂ → Bool
  | [] => true
  | a :: as => atomOk a && atomOkL as
def tmOk : Tm₂ → Bool
  | .ret a => atomOk a
  | .letE _ e₁ e₂ => tmOk e₁ && tmOk e₂
  | .letOp o as _ e => (decide (o = Op.load) || decide (o = Op.store)) && atomOkL as && tmOk e
  | .app a₁ a₂ => atomOk a₁ && atomOk a₂
  | .ite a e₁ e₂ => atomOk a && tmOk e₁ && tmOk e₂
  | .case a e₁ e₂ => atomOk a && tmOk e₁ && tmOk e₂
end

mutual
theorem atom_subst_ok {v : Atom₂} (hv : atomOk v = true) :
    ∀ (a : Atom₂) (k : Nat), atomOk a = true → atomOk (Atom.subst a k v) = true
  | .var n, k, _ => by
      simp only [Atom.subst]
      split_ifs <;> simp [atomOk, hv]
  | .const c, k, h => by simpa [Atom.subst] using h
  | .prim p as, k, h => by
      simp only [Atom.subst, atomOk] at h ⊢; exact atomL_subst_ok hv as k h
  | .lam τ e, k, h => by
      simp only [Atom.subst, atomOk] at h ⊢; exact tm_subst_ok hv e (k + 1) h
  | .fix τ₁ τ₂ e, k, h => by
      simp only [Atom.subst, atomOk] at h ⊢; exact tm_subst_ok hv e (k + 2) h
  | .pair a₁ a₂, k, h => by
      simp only [Atom.subst, atomOk, Bool.and_eq_true] at h ⊢
      exact ⟨atom_subst_ok hv a₁ k h.1, atom_subst_ok hv a₂ k h.2⟩
  | .fst a, k, h => by simp only [Atom.subst, atomOk] at h ⊢; exact atom_subst_ok hv a k h
  | .snd a, k, h => by simp only [Atom.subst, atomOk] at h ⊢; exact atom_subst_ok hv a k h
  | .inl τ a, k, h => by simp only [Atom.subst, atomOk] at h ⊢; exact atom_subst_ok hv a k h
  | .inr τ a, k, h => by simp only [Atom.subst, atomOk] at h ⊢; exact atom_subst_ok hv a k h
theorem atomL_subst_ok {v : Atom₂} (hv : atomOk v = true) :
    ∀ (as : List Atom₂) (k : Nat), atomOkL as = true → atomOkL (Atom.substL k v as) = true
  | [], _, _ => by simp [Atom.substL, atomOkL]
  | a :: as, k, h => by
      simp only [Atom.substL, atomOkL, Bool.and_eq_true] at h ⊢
      exact ⟨atom_subst_ok hv a k h.1, atomL_subst_ok hv as k h.2⟩
theorem tm_subst_ok {v : Atom₂} (hv : atomOk v = true) :
    ∀ (e : Tm₂) (k : Nat), tmOk e = true → tmOk (Tm.subst k v e) = true
  | .ret a, k, h => by simp only [Tm.subst, tmOk] at h ⊢; exact atom_subst_ok hv a k h
  | .letE τ e₁ e₂, k, h => by
      simp only [Tm.subst, tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨tm_subst_ok hv e₁ k h.1, tm_subst_ok hv e₂ (k + 1) h.2⟩
  | .letOp o as τ e, k, h => by
      simp only [Tm.subst, tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, atomL_subst_ok hv as k h.1.2⟩, tm_subst_ok hv e (k + 1) h.2⟩
  | .app a₁ a₂, k, h => by
      simp only [Tm.subst, tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨atom_subst_ok hv a₁ k h.1, atom_subst_ok hv a₂ k h.2⟩
  | .ite a e₁ e₂, k, h => by
      simp only [Tm.subst, tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨⟨atom_subst_ok hv a k h.1.1, tm_subst_ok hv e₁ k h.1.2⟩, tm_subst_ok hv e₂ k h.2⟩
  | .case a e₁ e₂, k, h => by
      simp only [Tm.subst, tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨⟨atom_subst_ok hv a k h.1.1, tm_subst_ok hv e₁ (k + 1) h.1.2⟩, tm_subst_ok hv e₂ (k + 1) h.2⟩
end

theorem const_ok_of_inR {c : Const} (h : Atom.inR₂ (.const c)) : atomOk (.const c) = true := by
  cases c <;> simp_all [Atom.inR₂, atomOk]

mutual
theorem eval_ok : ∀ (a : Atom₂) {v : Atom₂}, atomOk a = true → Atom.InR₂ a → Atom.eval a = some v → atomOk v = true
  | .var _, _, _, _, he => by simp [Atom.eval] at he
  | .const c, _, h, _, he => by simp only [Atom.eval, Option.some.injEq] at he; subst he; exact h
  | .prim p as, v, _, hi, he => by
      have hr := hi.2 v he
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨_, _, _, _, c, _, rfl⟩ := he
      exact const_ok_of_inR hr
  | .lam τ e, _, h, _, he => by simp only [Atom.eval, Option.some.injEq] at he; subst he; exact h
  | .fix τ₁ τ₂ e, _, h, _, he => by simp only [Atom.eval, Option.some.injEq] at he; subst he; exact h
  | .pair a₁ a₂, _, h, hi, he => by
      simp only [atomOk, Bool.and_eq_true] at h
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := he
      simp only [atomOk, Bool.and_eq_true]
      exact ⟨eval_ok a₁ h.1 hi.1 h₁, eval_ok a₂ h.2 hi.2 h₂⟩
  | .fst a, _, h, hi, he => by
      simp only [atomOk] at h
      simp only [Atom.eval, Option.bind_eq_some_iff] at he
      obtain ⟨w, hw, hm⟩ := he
      have := eval_ok a h hi hw
      cases w <;> simp_all [atomOk]
  | .snd a, _, h, hi, he => by
      simp only [atomOk] at h
      simp only [Atom.eval, Option.bind_eq_some_iff] at he
      obtain ⟨w, hw, hm⟩ := he
      have := eval_ok a h hi hw
      cases w <;> simp_all [atomOk]
  | .inl τ a, _, h, hi, he => by
      simp only [atomOk] at h
      simp only [Atom.eval, Option.map_eq_some_iff] at he
      obtain ⟨w, hw, rfl⟩ := he
      simp only [atomOk]; exact eval_ok a h hi hw
  | .inr τ a, _, h, hi, he => by
      simp only [atomOk] at h
      simp only [Atom.eval, Option.map_eq_some_iff] at he
      obtain ⟨w, hw, rfl⟩ := he
      simp only [atomOk]; exact eval_ok a h hi hw
theorem evalL_ok : ∀ (as : List Atom₂) {vs : List Atom₂}, atomOkL as = true → Atom.InRL₂ as → Atom.evalL as = some vs →
    atomOkL vs = true
  | [], _, _, _, he => by simp only [Atom.evalL, Option.some.injEq] at he; subst he; rfl
  | a :: as, _, h, hi, he => by
      simp only [atomOkL, Bool.and_eq_true] at h
      simp only [Atom.evalL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨v, hv, vs, hvs, rfl⟩ := he
      simp only [atomOkL, Bool.and_eq_true]
      exact ⟨eval_ok a h.1 hi.1 hv, evalL_ok as h.2 hi.2 hvs⟩
end

/-- The store invariant L-2 carries. -/
structure Shape (R₀ : Finmap (fun _ : Int => Nat)) (σ : Store) : Prop where
  reg : σ.R = R₀
  wf : σ.WF
  cells : CellsInR σ

theorem pure_ok : ∀ {e e' : Tm₂}, Step e e' → tmOk e = true → Tm.HeadInR e → tmOk e' = true
  | _, _, .letRet (a := a) (e₂ := e₂) hv, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h
      exact tm_subst_ok (eval_ok a h.1 hi hv) e₂ 0 h.2
  | _, _, .letStep hs, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h ⊢
      exact ⟨pure_ok hs h.1 hi, h.2⟩
  | _, _, .appLam (a₁ := a₁) (a₂ := a₂) (e := e) h₁ h₂, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h
      have hl := eval_ok a₁ h.1 hi.1 h₁
      simp only [atomOk] at hl
      exact tm_subst_ok (eval_ok a₂ h.2 hi.2 h₂) e 0 hl
  | _, _, .appFix (a₁ := a₁) (a₂ := a₂) (e := e) h₁ h₂, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h
      have hl := eval_ok a₁ h.1 hi.1 h₁
      have hb : tmOk e = true := by simpa only [atomOk] using hl
      exact tm_subst_ok hl _ 0 (tm_subst_ok (eval_ok a₂ h.2 hi.2 h₂) e 0 hb)
  | _, _, .iteT _ _, h, _ => by simp only [tmOk, Bool.and_eq_true] at h; exact h.1.2
  | _, _, .iteF _ _, h, _ => by simp only [tmOk, Bool.and_eq_true] at h; exact h.2
  | _, _, .caseL (a := a) (e₁ := e₁) hv, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h
      have := eval_ok a h.1.1 hi hv
      simp only [atomOk] at this
      exact tm_subst_ok this e₁ 0 h.1.2
  | _, _, .caseR (a := a) (e₂ := e₂) hv, h, hi => by
      simp only [tmOk, Bool.and_eq_true] at h
      have := eval_ok a h.1.1 hi hv
      simp only [atomOk] at this
      exact tm_subst_ok this e₂ 0 h.2

theorem opStep_load_inv {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .load vs σ = some (v, σ')) :
    ∃ p i w, Store.load p i σ = some w ∧ v = .const (.int w) ∧ σ' = σ := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [opStep] at h
  · simp [opStep] at h
  · cases a <;> cases b <;> simp [opStep] at h
    all_goals first
      | (rename_i c₁ c₂; cases c₁ <;> cases c₂ <;> simp [opStep] at h <;>
          (obtain ⟨w, hw, rfl, rfl⟩ := h; exact ⟨_, _, w, hw, rfl, rfl⟩))
      | (rename_i c₁; cases c₁ <;> simp [opStep] at h)
  · simp [opStep] at h

theorem opStep_store_inv {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .store vs σ = some (v, σ')) :
    ∃ p i w, vs = [.const (.cap p), .const (.int i), .const (.int w)] ∧ Store.store p i w σ = some σ' ∧
      v = .const (.cap p) := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [opStep] at h
  · simp [opStep] at h
  · simp [opStep] at h
  · cases a <;> try (simp [opStep] at h; done)
    rename_i c₁; cases c₁ <;> try (simp [opStep] at h; done)
    cases b <;> try (simp [opStep] at h; done)
    rename_i c₂; cases c₂ <;> try (simp [opStep] at h; done)
    cases c <;> try (simp [opStep] at h; done)
    rename_i c₃; cases c₃ <;> try (simp [opStep] at h; done)
    simp only [opStep, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨s, hs, rfl, rfl⟩ := h
    exact ⟨_, _, _, rfl, hs, rfl⟩
  · simp [opStep] at h

theorem op_ok {o : Op} {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} {R₀}
    (ho : o = Op.load ∨ o = Op.store) (hvs : atomOkL vs = true) (hS : Shape R₀ σ) (h : opStep o vs σ = some (v, σ')) :
    atomOk v = true ∧ Shape R₀ σ' := by
  rcases ho with rfl | rfl
  · obtain ⟨p, i, w, hw, rfl, rfl⟩ := opStep_load_inv h
    refine ⟨?_, hS⟩
    simp only [Store.load] at hw
    split at hw
    · split_ifs at hw; simp only [atomOk]; exact hS.cells _ _ hw
    · simp at hw
  · obtain ⟨p, i, w, rfl, hs, rfl⟩ := opStep_store_inv h
    have hwr : inRange w = true := by simp only [atomOkL, atomOk, Bool.and_eq_true, Bool.and_true] at hvs; exact hvs.2.2
    simp only [Store.store] at hs
    split at hs
    · rename_i n hn
      split_ifs at hs with hi
      simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨by simp [atomOk], ⟨hS.reg, ?_, ?_⟩⟩
      · have hk : (p + i) ∈ σ.H := (hS.wf.domH (p + i)).mpr ⟨p, n, hn, by simp [Store.InRegion]; omega⟩
        exact wf_insert_mem hk hS.wf
      · intro a u hu
        by_cases ha : a = p + i
        · subst ha; rw [Finmap.lookup_insert] at hu; cases hu; exact hwr
        · rw [Finmap.lookup_insert_of_ne _ ha] at hu; exact hS.cells _ _ hu
    · simp at hs

theorem step_ok : ∀ {c c' : Config}, Step₂ c c' → tmOk c.1 = true → Tm.HeadInR c.1 → ∀ {R₀}, Shape R₀ c.2 →
    tmOk c'.1 = true ∧ Shape R₀ c'.2
  | _, _, .pure hs, h, hi, _, hS => ⟨pure_ok hs h hi, hS⟩
  | _, _, .letStep hs, h, hi, _, hS => by
      simp only [tmOk, Bool.and_eq_true] at h ⊢
      obtain ⟨h1, h2⟩ := step_ok hs h.1 hi hS
      exact ⟨⟨h1, h.2⟩, h2⟩
  | _, _, .op (e := e) hev hop, h, hi, _, hS => by
      simp only [tmOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨hv, hS'⟩ := op_ok h.1.1 (evalL_ok _ h.1.2 hi hev) hS hop
      exact ⟨tm_subst_ok hv e 0 h.2, hS'⟩

/-- **L-2.** -/
theorem run_shape : ∀ {c c' : Config}, Steps₂ c c' → SrcInRange c → tmOk c.1 = true → ∀ {R₀}, Shape R₀ c.2 →
    tmOk c'.1 = true ∧ Shape R₀ c'.2
  | _, _, .refl _, _, h, _, hS => ⟨h, hS⟩
  | _, _, .step hs hr, hsrc, h, _, hS => by
      obtain ⟨h1, h2⟩ := step_ok hs h (hsrc _ (.refl _)) hS
      exact run_shape hr (fun S hS' => hsrc S (.step hs hS')) h1 h2

end K5
