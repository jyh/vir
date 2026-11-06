/-
  O95 layer L4, Lean arm (amend-21; DECLARATIONS addendum 5). N4-V, run_tokens₄ over EVERY interleaving, as a configuration
  invariant on ⟶₄ (OBJECT-L4 H5 (a)). The machinery first: `NT₄.cc`, a CLOSING compile (named → `Tm₄` under a total environment
  of constants), which names a thread's stages without changing any term (`NT₄.c` agrees with it on N4, `NT_c_eq_cc`).
-/
import VIRL4.Router4

namespace VIRL4
open VIRL1 VIRL2 VIRL3

/-! ## The closing compile. -/

end VIRL4

namespace VIRL3
open VIRL1 VIRL2 VIRL4

/-- A named atom in scope Γ, every name outside Γ replaced by its constant in ρ. -/
def NA.cc (ρ : String → Const₄) (Γ : List String) : NA → Atom₄
  | .v x => if x ∈ Γ then .var (Γ.idxOf x) else .const (ρ x)
  | .i n => .const (.c2 (.int n))
  | .p o a b => .prim o [NA.cc ρ Γ a, NA.cc ρ Γ b]

end VIRL3

namespace VIRL4
open VIRL1 VIRL2 VIRL3

def NT₄.cc (ρ : String → Const₄) (Γ : List String) : NT₄ → Tm₄
  | .ret a => .ret (NA.cc ρ Γ a)
  | .retU => .ret unitv
  | .letE x τ e₁ e₂ => .letE τ (e₁.cc ρ Γ) (e₂.cc ρ (x :: Γ))
  | .op x τ o as e => .letOp o (as.map (NA.cc ρ Γ)) τ (e.cc ρ (x :: Γ))
  | .ite a e₁ e₂ => .ite (NA.cc ρ Γ a) (e₁.cc ρ Γ) (e₂.cc ρ Γ)
  | .par x₁ x₂ τ₁ τ₂ e₁ e₂ e => .par τ₁ τ₂ (e₁.cc ρ Γ) (e₂.cc ρ Γ) (e.cc ρ (x₂ :: x₁ :: Γ))

end VIRL4

namespace VIRL3
open VIRL1 VIRL2 VIRL4

/-- Every name free in the term (outside Γ) satisfies S. -/
def NA.fvIn (S : String → Prop) (Γ : List String) : NA → Prop
  | .v x => x ∈ Γ ∨ S x
  | .i _ => True
  | .p _ a b => NA.fvIn S Γ a ∧ NA.fvIn S Γ b

end VIRL3

namespace VIRL4
open VIRL1 VIRL2 VIRL3

def NT₄.fvIn (S : String → Prop) (Γ : List String) : NT₄ → Prop
  | .ret a => a.fvIn S Γ
  | .retU => True
  | .letE x _ e₁ e₂ => e₁.fvIn S Γ ∧ e₂.fvIn S (x :: Γ)
  | .op x _ _ as e => (∀ a ∈ as, a.fvIn S Γ) ∧ e.fvIn S (x :: Γ)
  | .ite a e₁ e₂ => a.fvIn S Γ ∧ e₁.fvIn S Γ ∧ e₂.fvIn S Γ
  | .par x₁ x₂ _ _ e₁ e₂ e => e₁.fvIn S Γ ∧ e₂.fvIn S Γ ∧ e.fvIn S (x₂ :: x₁ :: Γ)

theorem idx_app_mem {y : String} {Γ : List String} (L : List String) (h : y ∈ Γ) :
    (Γ ++ L).idxOf y = Γ.idxOf y ∧ Γ.idxOf y < Γ.length := by
  induction Γ with
  | nil => simp at h
  | cons z Γ ih =>
    by_cases hz : z = y
    · subst hz; simp [List.idxOf_cons_self]
    · have hy : y ∈ Γ := by simpa [Ne.symm hz] using h
      obtain ⟨h1, h2⟩ := ih hy
      simp [List.idxOf_cons_ne _ hz, h1, h2]

theorem idx_app_nmem {y : String} {Γ : List String} (L : List String) (h : y ∉ Γ) :
    (Γ ++ L).idxOf y = Γ.length + L.idxOf y := by
  induction Γ with
  | nil => simp
  | cons z Γ ih =>
    have hz : z ≠ y := fun e => h (e ▸ List.mem_cons_self)
    have hy : y ∉ Γ := fun e => h (List.mem_cons_of_mem _ e)
    simp [List.idxOf_cons_ne _ hz, ih hy]; omega

/-- Substituting a constant for the binder x (at depth |Γ|, Δ outside it) is updating the environment at x. -/
theorem NA.cc_subst (ρ : String → Const₄) (x : String) (c : Const₄) (Γ Δ : List String) (hx : x ∉ Δ) :
    ∀ a : NA, (NA.cc ρ (Γ ++ x :: Δ) a).subst Γ.length (.const c) = NA.cc (Function.update ρ x c) (Γ ++ Δ) a
  | .v y => by
    by_cases hyΓ : y ∈ Γ
    · obtain ⟨h1, h2⟩ := idx_app_mem (x :: Δ) hyΓ
      obtain ⟨h1', _⟩ := idx_app_mem Δ hyΓ
      simp [NA.cc, hyΓ, h1, h1', Atom₄.subst, h2]
    · by_cases hyx : y = x
      · subst hyx
        have h1 := idx_app_nmem (y :: Δ) hyΓ
        simp [NA.cc, hyΓ, hx, h1, Atom₄.subst]
      · have h1 := idx_app_nmem (x :: Δ) hyΓ
        by_cases hyΔ : y ∈ Δ
        · have h2 := idx_app_nmem Δ hyΓ
          simp [NA.cc, hyΓ, hyΔ, h1, h2, Atom₄.subst, List.idxOf_cons_ne _ (Ne.symm hyx)]
        · simp [NA.cc, hyΓ, hyΔ, hyx, Atom₄.subst]
  | .i n => rfl
  | .p o a b => by
    simp only [NA.cc, Atom₄.subst, Atom₄.substL, NA.cc_subst ρ x c Γ Δ hx a, NA.cc_subst ρ x c Γ Δ hx b]

theorem substL_map {k : Nat} {v : Atom₄} {g : NA → Atom₄} :
    ∀ as : List NA, Atom₄.substL k v (as.map g) = as.map (fun a => (g a).subst k v)
  | [] => rfl
  | a :: as => by simp only [List.map, Atom₄.substL, substL_map as]

theorem NT₄.cc_subst (ρ : String → Const₄) (x : String) (c : Const₄) (Δ : List String) (hx : x ∉ Δ) :
    ∀ (e : NT₄) (Γ : List String),
      (e.cc ρ (Γ ++ x :: Δ)).subst Γ.length (.const c) = e.cc (Function.update ρ x c) (Γ ++ Δ)
  | .ret a, Γ => by simp only [NT₄.cc, Tm₄.subst, NA.cc_subst ρ x c Γ Δ hx a]
  | .retU, Γ => rfl
  | .letE y τ e₁ e₂, Γ => by
    have h2 := NT₄.cc_subst ρ x c Δ hx e₂ (y :: Γ)
    simp only [List.cons_append, List.length_cons] at h2
    simp only [NT₄.cc, Tm₄.subst, NT₄.cc_subst ρ x c Δ hx e₁ Γ, h2]
  | .op y τ o as e, Γ => by
    have h2 := NT₄.cc_subst ρ x c Δ hx e (y :: Γ)
    simp only [List.cons_append, List.length_cons] at h2
    simp only [NT₄.cc, Tm₄.subst, h2, substL_map, NA.cc_subst ρ x c Γ Δ hx]
  | .ite a e₁ e₂, Γ => by
    simp only [NT₄.cc, Tm₄.subst, NA.cc_subst ρ x c Γ Δ hx a, NT₄.cc_subst ρ x c Δ hx e₁ Γ, NT₄.cc_subst ρ x c Δ hx e₂ Γ]
  | .par y₁ y₂ τ₁ τ₂ e₁ e₂ e, Γ => by
    have h3 := NT₄.cc_subst ρ x c Δ hx e (y₂ :: y₁ :: Γ)
    simp only [List.cons_append, List.length_cons] at h3
    simp only [NT₄.cc, Tm₄.subst, NT₄.cc_subst ρ x c Δ hx e₁ Γ, NT₄.cc_subst ρ x c Δ hx e₂ Γ, h3]

/-- The step's own form: a constant bound by the innermost binder. -/
theorem NT₄.cc_subst0 (ρ : String → Const₄) (x : String) (c : Const₄) (e : NT₄) :
    (e.cc ρ [x]).subst 0 (.const c) = e.cc (Function.update ρ x c) [] :=
  NT₄.cc_subst ρ x c [] (by simp) e []

theorem NA.c_eq_cc (ρ : String → Const₄) (Γ : List String) :
    ∀ a : NA, a.fvIn (fun _ => False) Γ → NA.c₄ Γ a = NA.cc ρ Γ a
  | .v y, h => by
    simp only [NA.fvIn, or_false] at h
    simp [NA.c₄, NA.c, ιA, NA.cc, h]
  | .i n, _ => rfl
  | .p o a b, h => by
    have ha := NA.c_eq_cc ρ Γ a h.1
    have hb := NA.c_eq_cc ρ Γ b h.2
    simp only [NA.c₄, NA.c, ιA, ιL] at ha hb ⊢
    simp only [NA.cc, ha, hb]

theorem NT₄.c_eq_cc (ρ : String → Const₄) :
    ∀ (e : NT₄) (Γ : List String), e.fvIn (fun _ => False) Γ → e.c Γ = e.cc ρ Γ
  | .ret a, Γ, h => by simp only [NT₄.c, NT₄.cc, NA.c_eq_cc ρ Γ a h]
  | .retU, _, _ => rfl
  | .letE y τ e₁ e₂, Γ, h => by
    simp only [NT₄.c, NT₄.cc, NT₄.c_eq_cc ρ e₁ Γ h.1, NT₄.c_eq_cc ρ e₂ (y :: Γ) h.2]
  | .op y τ o as e, Γ, h => by
    have has : as.map (NA.c₄ Γ) = as.map (NA.cc ρ Γ) := List.map_congr_left fun a ha => NA.c_eq_cc ρ Γ a (h.1 a ha)
    simp only [NT₄.c, NT₄.cc, has, NT₄.c_eq_cc ρ e (y :: Γ) h.2]
  | .ite a e₁ e₂, Γ, h => by
    simp only [NT₄.c, NT₄.cc, NA.c_eq_cc ρ Γ a h.1, NT₄.c_eq_cc ρ e₁ Γ h.2.1, NT₄.c_eq_cc ρ e₂ Γ h.2.2]
  | .par y₁ y₂ τ₁ τ₂ e₁ e₂ e, Γ, h => by
    simp only [NT₄.c, NT₄.cc, NT₄.c_eq_cc ρ e₁ Γ h.1, NT₄.c_eq_cc ρ e₂ Γ h.2.1, NT₄.c_eq_cc ρ e (y₂ :: y₁ :: Γ) h.2.2]

theorem NA.cc_congr {S : String → Prop} {ρ ρ' : String → Const₄} (hρ : ∀ y, S y → ρ y = ρ' y) (Γ : List String) :
    ∀ a : NA, a.fvIn S Γ → NA.cc ρ Γ a = NA.cc ρ' Γ a
  | .v y, h => by
    by_cases hy : y ∈ Γ
    · simp [NA.cc, hy]
    · simp [NA.cc, hy, hρ y (h.resolve_left hy)]
  | .i _, _ => rfl
  | .p o a b, h => by simp only [NA.cc, NA.cc_congr hρ Γ a h.1, NA.cc_congr hρ Γ b h.2]

theorem NT₄.cc_congr {S : String → Prop} {ρ ρ' : String → Const₄} (hρ : ∀ y, S y → ρ y = ρ' y) :
    ∀ (e : NT₄) (Γ : List String), e.fvIn S Γ → e.cc ρ Γ = e.cc ρ' Γ
  | .ret a, Γ, h => by simp only [NT₄.cc, NA.cc_congr hρ Γ a h]
  | .retU, _, _ => rfl
  | .letE y τ e₁ e₂, Γ, h => by
    simp only [NT₄.cc, NT₄.cc_congr hρ e₁ Γ h.1, NT₄.cc_congr hρ e₂ (y :: Γ) h.2]
  | .op y τ o as e, Γ, h => by
    have has : as.map (NA.cc ρ Γ) = as.map (NA.cc ρ' Γ) := List.map_congr_left fun a ha => NA.cc_congr hρ Γ a (h.1 a ha)
    simp only [NT₄.cc, has, NT₄.cc_congr hρ e (y :: Γ) h.2]
  | .ite a e₁ e₂, Γ, h => by
    simp only [NT₄.cc, NA.cc_congr hρ Γ a h.1, NT₄.cc_congr hρ e₁ Γ h.2.1, NT₄.cc_congr hρ e₂ Γ h.2.2]
  | .par y₁ y₂ τ₁ τ₂ e₁ e₂ e, Γ, h => by
    simp only [NT₄.cc, NT₄.cc_congr hρ e₁ Γ h.1, NT₄.cc_congr hρ e₂ Γ h.2.1, NT₄.cc_congr hρ e (y₂ :: y₁ :: Γ) h.2.2]

/-! ## Steps of closed-compiled terms: every value a step binds is a constant. -/

theorem raiseV_const (v : Atom₂) : ∃ c, raiseV v = .const c := by
  cases v <;> simp [raiseV]

theorem opStep₄_const {o : Op₄} {vs : List Atom₄} {s : Store₄} {v : Atom₄} {s' : Store₄}
    (h : opStep₄ o vs s = some (v, s')) : ∃ c, v = .const c := by
  unfold opStep₄ at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, ⟨v₂, σ'⟩, _, he⟩ := h
    simp only [Prod.mk.injEq] at he
    rw [← he.1]; exact raiseV_const v₂
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩
  · split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    exact ⟨_, h.1.symm⟩
  · split at h
    · split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      exact ⟨_, h.1.symm⟩
    · simp at h
  · simp at h

theorem cc_op_step {ρ : String → Const₄} {x : String} {τ : Ty₄} {o : Op₄} {as : List NA} {e : NT₄} {s : Store₄}
    {T' : Tm₄} {s' : Store₄} (h : Step₄ ((NT₄.op x τ o as e).cc ρ [], s) (T', s')) :
    ∃ vs c, Atom₄.evalL (as.map (NA.cc ρ [])) = some vs ∧ opStep₄ o vs s = some (.const c, s') ∧
      T' = e.cc (Function.update ρ x c) [] := by
  simp only [NT₄.cc] at h
  cases h with
  | op h1 h2 =>
    obtain ⟨c, rfl⟩ := opStep₄_const h2
    exact ⟨_, c, h1, h2, NT₄.cc_subst0 ρ x c e⟩

theorem cc_ite_step {ρ : String → Const₄} {a : NA} {e₁ e₂ : NT₄} {s : Store₄} {T' : Tm₄} {s' : Store₄}
    (h : Step₄ ((NT₄.ite a e₁ e₂).cc ρ [], s) (T', s')) :
    ∃ c b, Atom₄.eval (NA.cc ρ [] a) = some (.const c) ∧ Const₄.toBool c = some b ∧ s' = s ∧
      T' = (if b then e₁.cc ρ [] else e₂.cc ρ []) := by
  simp only [NT₄.cc] at h
  cases h with
  | iteT h1 h2 => exact ⟨_, true, h1, h2, rfl, rfl⟩
  | iteF h1 h2 => exact ⟨_, false, h1, h2, rfl, rfl⟩

/-- The value of a named atom under ρ, when it has one, is a constant. -/
theorem eval_cc_const {ρ : String → Const₄} : ∀ (a : NA) {v : Atom₄}, Atom₄.eval (NA.cc ρ [] a) = some v → ∃ c, v = .const c
  | .v y, v, h => by simp [NA.cc, Atom₄.eval] at h; exact ⟨_, h.symm⟩
  | .i n, v, h => by simp [NA.cc, Atom₄.eval] at h; exact ⟨_, h.symm⟩
  | .p o a b, v, h => by
    simp only [NA.cc, Atom₄.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, c, _, rfl⟩ := h
    exact ⟨_, rfl⟩

theorem cc_letRet_step {ρ : String → Const₄} {x : String} {τ : Ty₄} {a : NA} {e : NT₄} {s : Store₄} {T' : Tm₄}
    {s' : Store₄} (h : Step₄ ((NT₄.letE x τ (.ret a) e).cc ρ [], s) (T', s')) :
    ∃ c, Atom₄.eval (NA.cc ρ [] a) = some (.const c) ∧ s' = s ∧ T' = e.cc (Function.update ρ x c) [] := by
  simp only [NT₄.cc] at h
  cases h with
  | letRet h1 =>
    obtain ⟨c, rfl⟩ := eval_cc_const a h1
    exact ⟨c, h1, rfl, NT₄.cc_subst0 ρ x c e⟩
  | letStep h1 => cases h1

/-! ## An L2 operation at L4 over a global store, read through its OpTriple (the result is the function's own). -/

theorem op4_inv {P : Assn} {o : Op} {vs : List Atom₄} {ws : List Atom₂} {Q : Atom₂ → Assn} {σ σf : Store}
    {L : List LockSt} {v : Atom₄} {s'' : Store₄} (hT : OpTriple P o ws Q) (hP : P σ) (hd : Store.Disj σ σf)
    (hwf : Store.WF (σ ⊎ σf)) (hvs : vs.mapM lowerV = some ws) (h : opStep₄ (.o2 o) vs ⟨σ ⊎ σf, L⟩ = some (v, s'')) :
    ∃ v₂ σq, v = raiseV v₂ ∧ s'' = ⟨σq ⊎ σf, L⟩ ∧ Store.Disj σq σf ∧ Store.WF (σq ⊎ σf) ∧ Q v₂ σq := by
  obtain ⟨v₂, σq, h1, h2, h3, h4⟩ := hT σ σf hP hd hwf
  simp only [opStep₄, hvs, Option.bind_some, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨v₂, σq, h.1.symm, h.2.symm, h2, h3, h4⟩

end VIRL4
