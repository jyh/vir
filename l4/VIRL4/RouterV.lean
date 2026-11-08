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

/-! ## The global store, one region in focus. -/

theorem swap12 {a b c : Store} (h : Store.Disj a b) : a ⊎ (b ⊎ c) = b ⊎ (a ⊎ c) := by
  rw [← Store.union_assoc, union_comm_disj h, Store.union_assoc]

theorem wload {p : Int} {n : Nat} {fc : Int → Int} {σm σx : Store} {L : List LockSt} {k : Int} {c : Const₄} {s' : Store₄}
    (hm : RegionAt p n fc σm) (hd : Store.Disj σm σx) (hwf : Store.WF (σm ⊎ σx)) (hk : 0 ≤ k ∧ k < n)
    (h : opStep₄ (.o2 .load) [capv p, c4 k] ⟨σm ⊎ σx, L⟩ = some (.const c, s')) :
    c = .c2 (.int (fc (p + k))) ∧ ∃ σq, s' = ⟨σq ⊎ σx, L⟩ ∧ RegionAt p n fc σq ∧ Store.Disj σq σx ∧ Store.WF (σq ⊎ σx) := by
  obtain ⟨v₂, σq, hv, hs, hdq, hwq, hc, hQ⟩ :=
    op4_inv (load_at p n fc k hk) hm hd hwf (ws := [.const (.cap p), .const (.int k)]) rfl h
  subst hc
  simp only [raiseV, Atom₄.const.injEq] at hv
  exact ⟨hv, σq, hs, hQ, hdq, hwq⟩

theorem wstore {p : Int} {n : Nat} {fc : Int → Int} {σm σx : Store} {L : List LockSt} {k v : Int} {c : Const₄}
    {s' : Store₄} (hm : RegionAt p n fc σm) (hd : Store.Disj σm σx) (hwf : Store.WF (σm ⊎ σx)) (hk : 0 ≤ k ∧ k < n)
    (h : opStep₄ (.o2 .store) [capv p, c4 k, c4 v] ⟨σm ⊎ σx, L⟩ = some (.const c, s')) :
    c = .c2 (.cap p) ∧ ∃ σq, s' = ⟨σq ⊎ σx, L⟩ ∧ RegionAt p n (Function.update fc (p + k) v) σq ∧ Store.Disj σq σx ∧
      Store.WF (σq ⊎ σx) := by
  obtain ⟨v₂, σq, hv, hs, hdq, hwq, hc, hQ⟩ :=
    op4_inv (store_at p n fc k v hk) hm hd hwf (ws := [.const (.cap p), .const (.int k), .const (.int v)]) rfl h
  subst hc
  simp only [raiseV, Atom₄.const.injEq] at hv
  exact ⟨hv, σq, hs, hQ, hdq, hwq⟩

/-! ## A thread's expected environment: the values its lets bind (t once read). -/

def ci (n : Int) : Const₄ := .c2 (.int n)

def envL (p q : Int) (f : Int → Int) (t : Int) (x : String) : Option Const₄ :=
  if x = "n" then some (ci (f (p + 0))) else
  if x = "magic0" then some (ci (f (p + 3))) else if x = "magic1" then some (ci (f (p + 4))) else
  if x = "magic2" then some (ci (f (p + 5))) else if x = "magic3" then some (ci (f (p + 6))) else
  if x = "magic" then some (ci (MgA f p)) else
  if x = "sender0" then some (ci (f (p + 7))) else if x = "sender1" then some (ci (f (p + 8))) else
  if x = "sender2" then some (ci (f (p + 9))) else if x = "sender3" then some (ci (f (p + 10))) else
  if x = "sender" then some (ci (SvA f p)) else
  if x = "topic0" then some (ci (f (p + 11))) else if x = "topic1" then some (ci (f (p + 12))) else
  if x = "topic2" then some (ci (f (p + 13))) else if x = "topic3" then some (ci (f (p + 14))) else
  if x = "topic" then some (ci (TvA f p)) else
  if x = "a" then some (ci (f (aclA f p))) else
  if x = "b" then some (.c2 (.cap q)) else if x = "t" then some (ci t) else if x = "b1" then some (.c2 (.cap q)) else
  if x = "r" then some (.c2 .unit) else if x = "w'" then some (.c2 (.cap p)) else if x = "w''" then some (.c2 (.cap p)) else
  none

def Env (w : String) (p : Int) (l : Nat) (q : Int) (f : Int → Int) (t : Int) (x : String) : Const₄ :=
  if x = "lb" then .lockv l else (envL p q f t x).getD (if x = w then .c2 (.cap p) else .c2 .unit)

/-- The two world names. -/
def WName (w : String) : Prop := w = "w1" ∨ w = "w2"

theorem Env_w {w : String} {p : Int} {l : Nat} {q : Int} {f : Int → Int} {t : Int} (hw : WName w) :
    Env w p l q f t w = .c2 (.cap p) := by
  rcases hw with rfl | rfl <;> simp [Env, envL]

theorem Env_upd_t {w : String} {p : Int} {l : Nat} {q : Int} {f : Int → Int} (hw : WName w) (t₀ t : Int) :
    Function.update (Env w p l q f t₀) "t" (.c2 (.int t)) = Env w p l q f t := by
  funext x
  by_cases hx : x = "t"
  · subst hx; simp [Env, envL, ci]
  · rw [Function.update_of_ne hx]
    rcases hw with rfl | rfl <;> simp [Env, envL, hx]

/-! ## The stages: suffixes of `Fn₄ w`. -/

def rd4 (_w : String) (_o : Int) (x : String) (k : NT₄) : NT₄ :=
  .letE x t4int (.ret (add (.v (x ++ "0")) (add (mul (.i 256) (.v (x ++ "1")))
    (add (mul (.i 65536) (.v (x ++ "2"))) (mul (.i 16777216) (.v (x ++ "3"))))))) k
def rd3 (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ := .op (x ++ "3") t4int (.o2 .load) [.v w, .i (6 + o)] (rd4 w o x k)
def rd2 (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ := .op (x ++ "2") t4int (.o2 .load) [.v w, .i (5 + o)] (rd3 w o x k)
def rd1 (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ := .op (x ++ "1") t4int (.o2 .load) [.v w, .i (4 + o)] (rd2 w o x k)
def rd0 (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ := .op (x ++ "0") t4int (.o2 .load) [.v w, .i (3 + o)] (rd1 w o x k)

theorem RD32₄_eq (w : String) (o : Int) (x : String) (k : NT₄) : RD32₄ w o x k = rd0 w o x k := rfl

def sH6 (w : String) : NT₄ := .op "r" t4unit .release [.v "lb", .v "b"] (EXIT₄ w 2)
def sEM1 : NT₄ := .op "w''" t4cap (.o2 .store) [.v "w'", .i 2, .i 24] (.ret (.v "w''"))
def sH5 (w : String) : NT₄ := .op "r" t4unit .release [.v "lb", .v "b1"] (EMIT₄ w)
def sH4 (w : String) : NT₄ := .op "b1" t4cap (.o2 .store) [.v "b", .v "sender", sub (.v "t") (.i 1)] (sH5 w)
def sH3 (w : String) : NT₄ :=
  .ite (conj (eq (.v "magic") (.i MAGIC)) (conj (eq (.v "a") (.i 1)) (lt (.i 0) (.v "t")))) (sH4 w) (sH6 w)
def sH2 (w : String) : NT₄ := .op "t" t4int (.o2 .load) [.v "b", .v "sender"] (sH3 w)
def sH1 (w : String) : NT₄ := .op "b" t4cap .acquire [.v "lb"] (sH2 w)
def sH0 (w : String) : NT₄ :=
  .op "a" t4int (.o2 .load) [.v w, add (.i A) (add (mul (.v "sender") (.i NTp)) (.v "topic"))] (sH1 w)
def sG2 (w : String) : NT₄ := rd0 w 8 "topic" (sH0 w)
def sG1 (w : String) : NT₄ := rd0 w 4 "sender" (sG2 w)
def sG0 (w : String) : NT₄ := rd0 w 0 "magic" (sG1 w)
def sF1 (w : String) : NT₄ := .ite (le (.i 24) (.v "n")) (sG0 w) (EXIT₄ w 1)
def sF0 (w : String) : NT₄ := .op "n" t4int (.o2 .load) [.v w, .i 0] (sF1 w)

theorem Fn₄_eq (w : String) : Fn₄ w = sF0 w := rfl

/-- The three RD32 blocks. -/
inductive RDK (w : String) : Int → String → NT₄ → Prop
  | m : RDK w 0 "magic" (sG1 w)
  | s : RDK w 4 "sender" (sG2 w)
  | t : RDK w 8 "topic" (sH0 w)

/-- The stages past the length test and before the acquire. -/
inductive PreS (w : String) : NT₄ → Prop
  | r0 {o x k} : RDK w o x k → PreS w (rd0 w o x k)
  | r1 {o x k} : RDK w o x k → PreS w (rd1 w o x k)
  | r2 {o x k} : RDK w o x k → PreS w (rd2 w o x k)
  | r3 {o x k} : RDK w o x k → PreS w (rd3 w o x k)
  | r4 {o x k} : RDK w o x k → PreS w (rd4 w o x k)
  | h0 : PreS w (sH0 w)
  | h1 : PreS w (sH1 w)

/-- The emit test inside the critical section, on the token t read there. -/
def Cond (f : Int → Int) (p t : Int) : Prop := MgA f p = MAGIC ∧ f (aclA f p) = 1 ∧ 0 < t

/-- A thread of N4 at a stage: its term, its world's contents fc, whether it holds ℓb, whether it has decremented its sender's
  bucket, and the token it read inside its critical section. -/
inductive Th (w : String) (p : Int) (l : Nat) (q : Int) (f : Int → Int) : Tm₄ → (Int → Int) → Bool → Bool → Option Int → Prop
  | f0 : Th w p l q f ((sF0 w).cc (Env w p l q f 0) []) f false false none
  | f1 : Th w p l q f ((sF1 w).cc (Env w p l q f 0) []) f false false none
  | pre {S} (h24 : 24 ≤ f (p + 0)) (hS : PreS w S) : Th w p l q f (S.cc (Env w p l q f 0) []) f false false none
  | cs0 (h24 : 24 ≤ f (p + 0)) : Th w p l q f ((sH2 w).cc (Env w p l q f 0) []) f true false none
  | cs1 (h24 : 24 ≤ f (p + 0)) (t : Int) : Th w p l q f ((sH3 w).cc (Env w p l q f t) []) f true false (some t)
  | cs2 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : Cond f p t) : Th w p l q f ((sH4 w).cc (Env w p l q f t) []) f true false (some t)
  | cs3 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : Cond f p t) : Th w p l q f ((sH5 w).cc (Env w p l q f t) []) f true true (some t)
  | cs4 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : ¬ Cond f p t) : Th w p l q f ((sH6 w).cc (Env w p l q f t) []) f true false (some t)
  | em0 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : Cond f p t) : Th w p l q f ((EMIT₄ w).cc (Env w p l q f t) []) f false true (some t)
  | em1 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : Cond f p t) :
      Th w p l q f (sEM1.cc (Env w p l q f t) []) (Function.update f (p + 1) 0) false true (some t)
  | em2 (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : Cond f p t) :
      Th w p l q f ((NT₄.ret (.v "w''")).cc (Env w p l q f t) []) (postF₄ f p t) false true (some t)
  | ex2a (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : ¬ Cond f p t) : Th w p l q f ((EXIT₄ w 2).cc (Env w p l q f t) []) f false false (some t)
  | ex2b (h24 : 24 ≤ f (p + 0)) (t : Int) (hc : ¬ Cond f p t) :
      Th w p l q f ((NT₄.ret (.v "w'")).cc (Env w p l q f t) []) (postF₄ f p t) false false (some t)
  | ex1a (hn : ¬ 24 ≤ f (p + 0)) : Th w p l q f ((EXIT₄ w 1).cc (Env w p l q f 0) []) f false false none
  | ex1b (hn : ¬ 24 ≤ f (p + 0)) : Th w p l q f ((NT₄.ret (.v "w'")).cc (Env w p l q f 0) []) (postF₄ f p 0) false false none

/-- What one step of a thread did to the shared state: nothing shared (a world op, a pure step, or the read of the token),
  the acquire, the release, or the decrement of the sender's bucket. -/
def Eff (S q : Int) (l : Nat) (L L' : List LockSt) (g g' : Int → Int) (h h' d d' : Bool) (tr tr' : Option Int) : Prop :=
  (L' = L ∧ g' = g ∧ h' = h ∧ d' = d ∧ (tr' = tr ∨ (tr = none ∧ h = true ∧ tr' = some (g (q + S))))) ∨
  (L[l]? = some (.free q) ∧ L' = L.set l (.held q) ∧ g' = g ∧ h = false ∧ h' = true ∧ d' = d ∧ tr' = tr ∧ tr = none) ∨
  (L' = L.set l (.free q) ∧ g' = g ∧ h = true ∧ h' = false ∧ d' = d ∧ tr' = tr) ∨
  (∃ t, L' = L ∧ h = true ∧ h' = true ∧ d = false ∧ d' = true ∧ tr = some t ∧ tr' = tr ∧ 0 < t ∧
    g' = Function.update g (q + S) (t - 1))

theorem cc_v (ρ : String → Const₄) (x : String) : NA.cc ρ [] (.v x) = .const (ρ x) := by simp [NA.cc]
theorem cc_i (ρ : String → Const₄) (n : Int) : NA.cc ρ [] (.i n) = .const (.c2 (.int n)) := rfl
theorem cc_p (ρ : String → Const₄) (o : L1.Prim) (a b : NA) : NA.cc ρ [] (.p o a b) = .prim o [NA.cc ρ [] a, NA.cc ρ [] b] := rfl

theorem upd_self {w : String} {p : Int} {l : Nat} {q : Int} {f : Int → Int} {t : Int} {x : String} {c : Const₄}
    (h : c = Env w p l q f t x) : Function.update (Env w p l q f t) x c = Env w p l q f t :=
  Function.update_eq_self_iff.2 h

theorem Th_ret_nostep {ρ : String → Const₄} {a : NA} {s : Store₄}
    {c' : Config₄} (h : Step₄ ((NT₄.ret a).cc ρ [], s) c') : False := by
  simp only [NT₄.cc] at h; cases h

theorem th_upd {w : String} {p : Int} {l : Nat} {q : Int} {f : Int → Int} {t : Int} {x : String} {c : Const₄} {e : NT₄}
    {fc : Int → Int} {h d : Bool} {tr : Option Int} (hc : c = Env w p l q f t x)
    (hT : Th w p l q f (e.cc (Env w p l q f t) []) fc h d tr) :
    Th w p l q f (e.cc (Function.update (Env w p l q f t) x c) []) fc h d tr := by
  rw [Function.update_eq_self_iff.2 hc]; exact hT

-- Structure of a step's atoms, then their values under the expected environment.
set_option hygiene false in
macro "evS" : tactic => `(tactic| (
  simp only [List.map, cc_v, cc_i, cc_p, add, sub, mul, le, lt, eq, conj, Env_w hw] at hev
  simp [Env, envL, ci, Atom₄.evalL, Atom₄.eval, constsOf₄, Const₄.toL1, Const.toL1, L1.Prim.interp, Const.ofL1,
    Const₄.toBool] at hev))

-- A load from the thread's own world at a constant index.
set_option hygiene false in
macro "wl" : tactic => `(tactic| (
  obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
  evS
  subst hev
  obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ := wload hm hd1 hwf ⟨by omega, by omega⟩ hop
  refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
  refine th_upd (by simp [Env, envL, ci]) ?_))

-- An RD32 sum.
set_option hygiene false in
macro "rs" : tactic => `(tactic| (
  obtain ⟨c, hev, rfl, rfl⟩ := cc_letRet_step hs
  evS
  subst hev
  refine ⟨_, _, _, _, σm, σb, g, L, ?_, rfl, hm, hb, hd1, hd2, hwf, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
  refine th_upd (by simp [Env, envL, ci, MgA, SvA, TvA]) ?_))

-- A store into the thread's own world at constant index and value.
set_option hygiene false in
macro "ws" : tactic => `(tactic| (
  obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
  evS
  subst hev
  obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ := wstore hm hd1 hwf ⟨by omega, by omega⟩ hop
  refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
  refine th_upd (by simp [Env, envL, ci]) ?_))

theorem disj_mb {σm σb σx : Store} (hd1 : Store.Disj σm (σb ⊎ σx)) : Store.Disj σm σb :=
  ((Store.disj_union_right _ _ _).1 hd1).1

theorem disj_b_mx {σm σb σx : Store} (hd1 : Store.Disj σm (σb ⊎ σx)) (hd2 : Store.Disj σb σx) :
    Store.Disj σb (σm ⊎ σx) :=
  (Store.disj_union_right _ _ _).2 ⟨disj_symm (disj_mb hd1), hd2⟩

theorem disj_mx {σm σb σx : Store} (hd1 : Store.Disj σm (σb ⊎ σx)) : Store.Disj σm σx :=
  ((Store.disj_union_right _ _ _).1 hd1).2

theorem back_m_bx {σm σq σx : Store} (hdq : Store.Disj σq (σm ⊎ σx)) (hmx : Store.Disj σm σx) :
    Store.Disj σm (σq ⊎ σx) ∧ Store.Disj σq σx := by
  obtain ⟨h1, h2⟩ := (Store.disj_union_right _ _ _).1 hdq
  exact ⟨(Store.disj_union_right _ _ _).2 ⟨disj_symm h1, hmx⟩, h2⟩

theorem bload {q : Int} {g : Int → Int} {σm σb σx : Store} {L : List LockSt} {k : Int} {c : Const₄} {s' : Store₄}
    (hb : RegionAt q 4 g σb) (hd1 : Store.Disj σm (σb ⊎ σx)) (hd2 : Store.Disj σb σx) (hwf : Store.WF (σm ⊎ (σb ⊎ σx)))
    (hk : 0 ≤ k ∧ k < 4) (h : opStep₄ (.o2 .load) [capv q, c4 k] ⟨σm ⊎ (σb ⊎ σx), L⟩ = some (.const c, s')) :
    c = .c2 (.int (g (q + k))) ∧ ∃ σq, s' = ⟨σm ⊎ (σq ⊎ σx), L⟩ ∧ RegionAt q 4 g σq ∧ Store.Disj σm (σq ⊎ σx) ∧
      Store.Disj σq σx ∧ Store.WF (σm ⊎ (σq ⊎ σx)) := by
  rw [swap12 (disj_mb hd1)] at h hwf
  obtain ⟨hc, σq, rfl, hq, hdq, hwq⟩ := wload hb (disj_b_mx hd1 hd2) hwf (by exact_mod_cast hk) h
  obtain ⟨d1, d2⟩ := back_m_bx hdq (disj_mx hd1)
  have hsw := swap12 (c := σx) (disj_symm ((Store.disj_union_right _ _ _).1 hdq).1)
  refine ⟨hc, σq, by rw [← hsw], hq, d1, d2, by rw [hsw]; exact hwq⟩

theorem bstore {q : Int} {g : Int → Int} {σm σb σx : Store} {L : List LockSt} {k v : Int} {c : Const₄} {s' : Store₄}
    (hb : RegionAt q 4 g σb) (hd1 : Store.Disj σm (σb ⊎ σx)) (hd2 : Store.Disj σb σx) (hwf : Store.WF (σm ⊎ (σb ⊎ σx)))
    (hk : 0 ≤ k ∧ k < 4) (h : opStep₄ (.o2 .store) [capv q, c4 k, c4 v] ⟨σm ⊎ (σb ⊎ σx), L⟩ = some (.const c, s')) :
    c = .c2 (.cap q) ∧ ∃ σq, s' = ⟨σm ⊎ (σq ⊎ σx), L⟩ ∧ RegionAt q 4 (Function.update g (q + k) v) σq ∧
      Store.Disj σm (σq ⊎ σx) ∧ Store.Disj σq σx ∧ Store.WF (σm ⊎ (σq ⊎ σx)) := by
  rw [swap12 (disj_mb hd1)] at h hwf
  obtain ⟨hc, σq, rfl, hq, hdq, hwq⟩ := wstore hb (disj_b_mx hd1 hd2) hwf (by exact_mod_cast hk) h
  obtain ⟨d1, d2⟩ := back_m_bx hdq (disj_mx hd1)
  have hsw := swap12 (c := σx) (disj_symm ((Store.disj_union_right _ _ _).1 hdq).1)
  refine ⟨hc, σq, by rw [← hsw], hq, d1, d2, by rw [hsw]; exact hwq⟩

set_option maxHeartbeats 1000000 in
/-- ONE THREAD'S STEP, by stage: from any global store holding its world, the bucket region and any rest, the step lands in the next
  stage with the store re-split the same way, and does to the shared state exactly one of the four things `Eff` names. -/
theorem th_step {w : String} {p : Int} {l : Nat} {q : Int} {f fc : Int → Int} {T : Tm₄} {hold dec : Bool} {tr : Option Int}
    {σm σb σx : Store} {g : Int → Int} {L : List LockSt} {T' : Tm₄} {s' : Store₄}
    (hw : WName w) (hS : 0 ≤ SvA f p ∧ SvA f p < 4 ∧ 0 ≤ TvA f p ∧ TvA f p < 4)
    (hT : Th w p l q f T fc hold dec tr)
    (hm : RegionAt p 83 fc σm) (hb : RegionAt q 4 g σb) (hd1 : Store.Disj σm (σb ⊎ σx)) (hd2 : Store.Disj σb σx)
    (hwf : Store.WF (σm ⊎ (σb ⊎ σx)))
    (hL : L[l]? = some (.free q) ∨ L[l]? = some (.held q)) (hhold : hold = true → L[l]? = some (.held q))
    (hs : Step₄ (T, ⟨σm ⊎ (σb ⊎ σx), L⟩) (T', s')) :
    ∃ fc' hold' dec' tr' σm' σb' g' L', Th w p l q f T' fc' hold' dec' tr' ∧ s' = ⟨σm' ⊎ (σb' ⊎ σx), L'⟩ ∧
      RegionAt p 83 fc' σm' ∧ RegionAt q 4 g' σb' ∧ Store.Disj σm' (σb' ⊎ σx) ∧ Store.Disj σb' σx ∧
      Store.WF (σm' ⊎ (σb' ⊎ σx)) ∧ Eff (SvA f p) q l L L' g g' hold hold' dec dec' tr tr' := by
  obtain ⟨hs0, hs4, ht0, ht4⟩ := hS
  cases hT with
  | f0 => wl; exact Th.f1
  | f1 =>
    obtain ⟨c, b, hev, hbool, rfl, rfl⟩ := cc_ite_step hs
    evS
    subst hev
    simp [Const₄.toBool] at hbool
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      refine ⟨_, _, _, _, σm, σb, g, L, ?_, rfl, hm, hb, hd1, hd2, hwf, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
    · exact Th.ex1a (by simpa using hbool)
    · exact Th.pre (by simpa using hbool) (PreS.r0 RDK.m)
  | pre h24 hS =>
    cases hS with
    | r0 hk => cases hk <;> (wl; exact Th.pre h24 (PreS.r1 (by constructor)))
    | r1 hk => cases hk <;> (wl; exact Th.pre h24 (PreS.r2 (by constructor)))
    | r2 hk => cases hk <;> (wl; exact Th.pre h24 (PreS.r3 (by constructor)))
    | r3 hk => cases hk <;> (wl; exact Th.pre h24 (PreS.r4 (by constructor)))
    | r4 hk =>
      cases hk
      · rs; exact Th.pre h24 (PreS.r0 RDK.s)
      · rs; exact Th.pre h24 (PreS.r0 RDK.t)
      · rs; exact Th.pre h24 PreS.h0
    | h0 =>
      obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
      evS
      subst hev
      obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ :=
        wload hm hd1 hwf ⟨by simp only [A, NW, NTp]; omega, by simp only [A, NW, NTp]; push_cast; omega⟩ hop
      refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
      refine th_upd (by simp [Env, envL, ci, aclA, A, NW, NTp]) ?_
      exact Th.pre h24 PreS.h1
    | h1 =>
      obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
      evS
      subst hev
      rcases hL with hf | hh
      · simp [opStep₄, hf, capv] at hop
        obtain ⟨rfl, rfl⟩ := hop
        refine ⟨f, true, false, none, σm, σb, g, _, ?_, rfl, hm, hb, hd1, hd2, hwf,
          Or.inr (Or.inl ⟨hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩
        refine th_upd (by simp [Env, envL, ci]) ?_
        exact Th.cs0 h24
      · simp [opStep₄, hh] at hop
  | cs0 h24 =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    obtain ⟨rfl, σq, rfl, hq, d1, d2, hwq⟩ := bload hb hd1 hd2 hwf ⟨hs0, hs4⟩ hop
    refine ⟨f, true, false, some (g (q + SvA f p)), σm, σq, g, L, ?_, rfl, hm, hq, d1, d2, hwq,
      Or.inl ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩
    rw [Env_upd_t hw]
    exact Th.cs1 h24 _
  | cs1 h24 t =>
    obtain ⟨c, b, hev, hbool, rfl, rfl⟩ := cc_ite_step hs
    evS
    subst hev
    simp [Const₄.toBool] at hbool
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      refine ⟨_, _, _, _, σm, σb, g, L, ?_, rfl, hm, hb, hd1, hd2, hwf, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
    · exact Th.cs4 h24 t (by simpa [Cond] using hbool)
    · exact Th.cs2 h24 t (by simpa [Cond] using hbool)
  | cs2 h24 t hc =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    obtain ⟨rfl, σq, rfl, hq, d1, d2, hwq⟩ := bstore hb hd1 hd2 hwf ⟨hs0, hs4⟩ hop
    refine ⟨f, true, true, some t, σm, σq, _, L, ?_, rfl, hm, hq, d1, d2, hwq,
      Or.inr (Or.inr (Or.inr ⟨t, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hc.2.2, rfl⟩))⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.cs3 h24 t hc
  | cs3 h24 t hc =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    simp [opStep₄, hhold rfl, unitv] at hop
    obtain ⟨rfl, rfl⟩ := hop
    refine ⟨f, false, true, some t, σm, σb, g, _, ?_, rfl, hm, hb, hd1, hd2, hwf,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.em0 h24 t hc
  | cs4 h24 t hc =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    simp [opStep₄, hhold rfl, unitv] at hop
    obtain ⟨rfl, rfl⟩ := hop
    refine ⟨f, false, false, some t, σm, σb, g, _, ?_, rfl, hm, hb, hd1, hd2, hwf,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.ex2a h24 t hc
  | em0 h24 t hc => ws; exact Th.em1 h24 t hc
  | em1 h24 t hc =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ := wstore hm hd1 hwf ⟨by omega, by omega⟩ hop
    have hpf : Function.update (Function.update f (p + 1) 0) (p + 2) 24 = postF₄ f p t := by
      unfold Cond at hc
      have h24' : 24 ≤ f p := by simpa using h24
      simp [postF₄, h24', hc]
    rw [hpf] at hq
    refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.em2 h24 t hc
  | em2 => exact (Th_ret_nostep hs).elim
  | ex2a h24 t hc =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ := wstore hm hd1 hwf ⟨by omega, by omega⟩ hop
    have hpf : Function.update f (p + 1) 2 = postF₄ f p t := by
      unfold Cond at hc
      have h24' : 24 ≤ f p := by simpa using h24
      simp [postF₄, h24', hc]
    rw [hpf] at hq
    refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.ex2b h24 t hc
  | ex2b => exact (Th_ret_nostep hs).elim
  | ex1a hn =>
    obtain ⟨vs, c, hev, hop, rfl⟩ := cc_op_step hs
    evS
    subst hev
    obtain ⟨rfl, σq, rfl, hq, hdq, hwq⟩ := wstore hm hd1 hwf ⟨by omega, by omega⟩ hop
    have hpf : Function.update f (p + 1) 1 = postF₄ f p 0 := by
      have hn' : ¬ 24 ≤ f p := by simpa using hn
      simp [postF₄, hn']
    rw [hpf] at hq
    refine ⟨_, _, _, _, σq, σb, g, L, ?_, rfl, hq, hb, hdq, hd2, hwq, Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩⟩
    refine th_upd (by simp [Env, envL, ci]) ?_
    exact Th.ex1b hn
  | ex1b => exact (Th_ret_nostep hs).elim

/-! ## A thread at `ret`: its world holds `postF₄` for the token it read, and it decremented exactly when it emits. -/

/-- L3's `Emits` with the token t read inside the critical section in place of `0 < f (bktA f p)` (addendum 5). -/
abbrev EmitsT (f : Int → Int) (p t : Int) : Prop := 24 ≤ f (p + 0) ∧ MgA f p = MAGIC ∧ f (aclA f p) = 1 ∧ 0 < t

theorem th_ret {w : String} {p : Int} {l : Nat} {q : Int} {f fc : Int → Int} {T : Tm₄} {h d : Bool} {tr : Option Int}
    {a : Atom₄} (hT : Th w p l q f T fc h d tr) (hr : T = .ret a) :
    (∃ t, fc = postF₄ f p t ∧ (d = true ↔ EmitsT f p t) ∧ h = false) ∧ (∀ v, Atom₄.eval a = some v → ∃ c, v = .const c) := by
  cases hT with
  | em2 h24 t hc =>
    simp only [NT₄.cc, Tm₄.ret.injEq] at hr; subst hr
    have h24' : 24 ≤ f p := by simpa using h24
    exact ⟨⟨t, rfl, by simp [EmitsT, h24', hc.1, hc.2.1, hc.2.2], rfl⟩, fun v hv => eval_cc_const _ hv⟩
  | ex2b h24 t hc =>
    simp only [NT₄.cc, Tm₄.ret.injEq] at hr; subst hr
    refine ⟨⟨t, rfl, ?_, rfl⟩, fun v hv => eval_cc_const _ hv⟩
    simp only [Bool.false_eq_true, false_iff]
    exact fun he => hc ⟨he.2.1, he.2.2.1, he.2.2.2⟩
  | ex1b hn =>
    simp only [NT₄.cc, Tm₄.ret.injEq] at hr; subst hr
    refine ⟨⟨0, rfl, ?_, rfl⟩, fun v hv => eval_cc_const _ hv⟩
    simp only [Bool.false_eq_true, false_iff]
    exact fun he => hn he.1
  | pre _ hS => cases hS <;> simp [NT₄.cc, rd0, rd1, rd2, rd3, rd4, sH0, sH1] at hr
  | _ => simp [NT₄.cc, sF0, sF1, sH2, sH3, sH4, sH5, sH6, EMIT₄, EXIT₄, sEM1] at hr

/-! ## The configuration invariant over both threads (H5 (a)). -/

/-- N4's par body: free the two returned worlds. -/
def BN : NT₄ := .op "u1" t4unit (.o2 .free) [.v "w1'"] (.op "u2" t4unit (.o2 .free) [.v "w2'"] .retU)

theorem N4n_eq : N4n = .par "w1'" "w2'" t4cap t4cap (Fn₄ "w1") (Fn₄ "w2") BN := rfl

/-- A thread's decrement naming s, as a count. -/
def cnt (d : Bool) (S s : Int) : Int := if d = true ∧ S = s then 1 else 0

/-- A frame's sender and topic in range (L3's layout facts, as R4 and F₄_S take them). -/
def InR (f : Int → Int) (p : Int) : Prop := 0 ≤ SvA f p ∧ SvA f p < 4 ∧ 0 ≤ TvA f p ∧ TvA f p < 4

/-- THE INVARIANT: both threads at stages; the store re-split as world 1 · bucket · world 2 · frame; ℓb held exactly when a thread
  is inside its critical section, never both; every bucket ≥ 0 and bucket + decrements naming s = g₀(q + s); a thread that read t
  inside its critical section and has not decremented sees its sender's bucket = t. After the join: the body's frees. -/
inductive R4 (p₁ p₂ q : Int) (l : Nat) (f₁ f₂ g₀ : Int → Int) (ρ₀ : String → Const₄) : Config₄ → Prop where
  | par {T₁ T₂ : Tm₄} {fc₁ fc₂ g : Int → Int} {h₁ h₂ d₁ d₂ : Bool} {tr₁ tr₂ : Option Int} {σ₁ σ₂ σb σF : Store}
      {L : List LockSt} :
      Th "w1" p₁ l q f₁ T₁ fc₁ h₁ d₁ tr₁ → Th "w2" p₂ l q f₂ T₂ fc₂ h₂ d₂ tr₂ →
      RegionAt p₁ 83 fc₁ σ₁ → RegionAt p₂ 83 fc₂ σ₂ → RegionAt q 4 g σb →
      Store.Disj σ₁ (σb ⊎ (σ₂ ⊎ σF)) → Store.Disj σb (σ₂ ⊎ σF) → Store.Disj σ₂ σF →
      Store.WF (σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF))) →
      L[l]? = some (if h₁ || h₂ then .held q else .free q) → ¬ (h₁ = true ∧ h₂ = true) →
      (∀ s, 0 ≤ s → s < 4 → 0 ≤ g (q + s) ∧ g (q + s) + cnt d₁ (SvA f₁ p₁) s + cnt d₂ (SvA f₂ p₂) s = g₀ (q + s)) →
      (∀ t, tr₁ = some t → d₁ = false → h₁ = true → g (q + SvA f₁ p₁) = t) →
      (∀ t, tr₂ = some t → d₂ = false → h₂ = true → g (q + SvA f₂ p₂) = t) →
      R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ (.par t4cap t4cap T₁ T₂ (BN.cc ρ₀ ["w2'", "w1'"]), ⟨σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF)), L⟩)
  | post {ρ : String → Const₄} {s : Store₄} {e : NT₄} :
      (e = BN ∨ e = .op "u2" t4unit (.o2 .free) [.v "w2'"] .retU ∨ e = .retU) → R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ (e.cc ρ [], s)

theorem set_get {L : List LockSt} {l : Nat} {x y : LockSt} (h : L[l]? = some x) : (L.set l y)[l]? = some y := by
  have hl := (List.getElem?_eq_some_iff.1 h).1
  simp [hl]

theorem lock_cases {L : List LockSt} {l : Nat} {q : Int} {b : Bool}
    (h : L[l]? = some (if b then .held q else .free q)) : L[l]? = some (.free q) ∨ L[l]? = some (.held q) := by
  cases b <;> simp_all

/-- The decrement keeps the count: sender S's bucket goes from t to t − 1 exactly as its decrements go up by one. -/
theorem cnt_dec {g : Int → Int} {g₀ : Int → Int} {q S t : Int} {d₂ : Bool} {S₂ : Int} (ht : g (q + S) = t) (h0 : 0 < t)
    (hc : ∀ s, 0 ≤ s → s < 4 → 0 ≤ g (q + s) ∧ g (q + s) + cnt false S s + cnt d₂ S₂ s = g₀ (q + s)) :
    ∀ s, 0 ≤ s → s < 4 → 0 ≤ Function.update g (q + S) (t - 1) (q + s) ∧
      Function.update g (q + S) (t - 1) (q + s) + cnt true S s + cnt d₂ S₂ s = g₀ (q + s) := by
  intro s hs0 hs4
  obtain ⟨h1, h2⟩ := hc s hs0 hs4
  by_cases hs : S = s
  · subst hs
    simp only [Function.update_self, cnt] at h2 ⊢
    simp at h2 ⊢
    constructor <;> omega
  · have hne : q + s ≠ q + S := by omega
    simp only [Function.update_of_ne hne, cnt] at h2 ⊢
    simp [hs] at h2 ⊢
    exact ⟨h1, h2⟩

theorem rot {a b c d : Store} (hab : Store.Disj a b) (hac : Store.Disj a c) (hbc : Store.Disj b c) :
    a ⊎ (b ⊎ (c ⊎ d)) = c ⊎ (b ⊎ (a ⊎ d)) := by
  rw [swap12 hab, swap12 (c := d) hac, swap12 hbc]

set_option maxHeartbeats 1000000 in
/-- The invariant is preserved by every ⟶₄ step: either side's (by `th_step`, with the store rotated for the right side), or the join. -/
theorem R4_step {p₁ p₂ q : Int} {l : Nat} {f₁ f₂ g₀ : Int → Int} {ρ₀ : String → Const₄} (hr₁ : InR f₁ p₁)
    (hr₂ : InR f₂ p₂) {c c' : Config₄} (hr : R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ c) (hs : Step₄ c c') :
    R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ c' := by
  cases hr with
  | @par T₁ T₂ fc₁ fc₂ g h₁ h₂ d₁ d₂ tr₁ tr₂ σ₁ σ₂ σb σF L hT₁ hT₂ hR1 hR2 hRb D1 D2 D3 hwf hLk hmx hcnt htr1 htr2 =>
    have hLc := lock_cases hLk
    cases hs with
    | @parL _ _ _ T₁' _ _ _ s' h =>
      have hh₁ : h₁ = true → L[l]? = some (.held q) := fun e => by rw [hLk, e]; simp
      obtain ⟨fc', h', d', tr', σm', σb', g', L', hT', rfl, hm', hb', hd1', hd2', hwf', heff⟩ :=
        th_step (Or.inl rfl) hr₁ hT₁ hR1 hRb D1 D2 hwf hLc hh₁ h
      rcases heff with ⟨rfl, rfl, rfl, rfl, htr⟩ | ⟨hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
        ⟨t, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, rfl⟩
      · refine R4.par hT' hT₂ hm' hR2 hb' hd1' hd2' D3 hwf' hLk hmx hcnt ?_ htr2
        rcases htr with rfl | ⟨rfl, -, rfl⟩
        · exact htr1
        · intro t ht _ _; simp at ht; exact ht
      · have : h₂ = false := by rw [hf] at hLk; cases h₂ <;> simp_all
        subst this
        exact R4.par hT' hT₂ hm' hR2 hb' hd1' hd2' D3 hwf' (by simpa using set_get hf) (by simp) hcnt
          (fun _ h => by simp at h) htr2
      · have : h₂ = false := by cases h₂ <;> simp_all
        subst this
        exact R4.par hT' hT₂ hm' hR2 hb' hd1' hd2' D3 hwf' (by simpa using set_get hLk) (by simp) hcnt
          (fun _ _ _ h => by simp at h) htr2
      · have : h₂ = false := by cases h₂ <;> simp_all
        subst this
        exact R4.par hT' hT₂ hm' hR2 hb' hd1' hd2' D3 hwf' hLk (by simp) (cnt_dec (htr1 t rfl rfl rfl) ht hcnt)
          (fun _ _ h => by simp at h) (fun _ _ _ h => by simp at h)
    | @parR _ _ _ _ T₂' _ _ s' h =>
      have hh₂ : h₂ = true → L[l]? = some (.held q) := fun e => by rw [hLk, e]; simp
      obtain ⟨h1b, h12, h1F⟩ : Store.Disj σ₁ σb ∧ Store.Disj σ₁ σ₂ ∧ Store.Disj σ₁ σF := by
        simp only [Store.disj_union_right] at D1; exact ⟨D1.1, D1.2.1, D1.2.2⟩
      obtain ⟨hb2, hbF⟩ : Store.Disj σb σ₂ ∧ Store.Disj σb σF := by
        simp only [Store.disj_union_right] at D2; exact D2
      have hrot := rot (d := σF) h1b h12 hb2
      have E1 : Store.Disj σ₂ (σb ⊎ (σ₁ ⊎ σF)) := by
        simp only [Store.disj_union_right]; exact ⟨disj_symm hb2, disj_symm h12, D3⟩
      have E2 : Store.Disj σb (σ₁ ⊎ σF) := by simp only [Store.disj_union_right]; exact ⟨disj_symm h1b, hbF⟩
      rw [hrot] at h hwf
      obtain ⟨fc', h', d', tr', σm', σb', g', L', hT', rfl, hm', hb', hd1', hd2', hwf', heff⟩ :=
        th_step (Or.inr rfl) hr₂ hT₂ hR2 hRb E1 E2 hwf hLc hh₂ h
      obtain ⟨k2b, k21, k2F⟩ : Store.Disj σm' σb' ∧ Store.Disj σm' σ₁ ∧ Store.Disj σm' σF := by
        simp only [Store.disj_union_right] at hd1'; exact ⟨hd1'.1, hd1'.2.1, hd1'.2.2⟩
      obtain ⟨kb1, kbF⟩ : Store.Disj σb' σ₁ ∧ Store.Disj σb' σF := by
        simp only [Store.disj_union_right] at hd2'; exact hd2'
      have hback := rot (d := σF) k2b k21 kb1
      have F1 : Store.Disj σ₁ (σb' ⊎ (σm' ⊎ σF)) := by
        simp only [Store.disj_union_right]; exact ⟨disj_symm kb1, disj_symm k21, h1F⟩
      have F2 : Store.Disj σb' (σm' ⊎ σF) := by simp only [Store.disj_union_right]; exact ⟨disj_symm k2b, kbF⟩
      rw [hback] at hwf' ⊢
      have hcnt' : ∀ {g'' : Int → Int} {d₂'' : Bool},
          (∀ s, 0 ≤ s → s < 4 → 0 ≤ g'' (q + s) ∧ g'' (q + s) + cnt d₂'' (SvA f₂ p₂) s + cnt d₁ (SvA f₁ p₁) s = g₀ (q + s)) →
          (∀ s, 0 ≤ s → s < 4 → 0 ≤ g'' (q + s) ∧ g'' (q + s) + cnt d₁ (SvA f₁ p₁) s + cnt d₂'' (SvA f₂ p₂) s = g₀ (q + s)) :=
        fun h s a b => ⟨(h s a b).1, by have := (h s a b).2; omega⟩
      have hcntS : ∀ s, 0 ≤ s → s < 4 → 0 ≤ g (q + s) ∧ g (q + s) + cnt d₂ (SvA f₂ p₂) s + cnt d₁ (SvA f₁ p₁) s = g₀ (q + s) :=
        fun s a b => ⟨(hcnt s a b).1, by have := (hcnt s a b).2; omega⟩
      rcases heff with ⟨rfl, rfl, rfl, rfl, htr⟩ | ⟨hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
        ⟨t, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, rfl⟩
      · refine R4.par hT₁ hT' hR1 hm' hb' F1 F2 k2F hwf' hLk hmx hcnt htr1 ?_
        rcases htr with rfl | ⟨rfl, -, rfl⟩
        · exact htr2
        · intro t ht _ _; simp at ht; exact ht
      · have : h₁ = false := by rw [hf] at hLk; cases h₁ <;> simp_all
        subst this
        exact R4.par hT₁ hT' hR1 hm' hb' F1 F2 k2F hwf' (by simpa using set_get hf) (by simp) hcnt
          (fun _ _ _ h => by simp at h) (fun _ h => by simp at h)
      · have : h₁ = false := by cases h₁ <;> simp_all
        subst this
        exact R4.par hT₁ hT' hR1 hm' hb' F1 F2 k2F hwf' (by simpa using set_get hLk) (by simp) hcnt
          htr1 (fun _ _ _ h => by simp at h)
      · have : h₁ = false := by cases h₁ <;> simp_all
        subst this
        exact R4.par hT₁ hT' hR1 hm' hb' F1 F2 k2F hwf' hLk (by simp)
          (hcnt' (cnt_dec (htr2 t rfl rfl rfl) ht hcntS)) (fun _ _ _ h => by simp at h) (fun _ _ h => by simp at h)
    | @parDone _ _ a₁ a₂ v₁ v₂ _ _ hv₁ hv₂ =>
      obtain ⟨-, hc₁⟩ := th_ret hT₁ rfl
      obtain ⟨-, hc₂⟩ := th_ret hT₂ rfl
      obtain ⟨c₁, rfl⟩ := hc₁ v₁ hv₁
      obtain ⟨c₂, rfl⟩ := hc₂ v₂ hv₂
      have e1 := NT₄.cc_subst ρ₀ "w2'" c₂ ["w1'"] (by simp) BN []
      simp only [List.nil_append, List.length_nil] at e1
      rw [e1, NT₄.cc_subst0]
      exact R4.post (Or.inl rfl)
  | @post ρ s e he =>
    obtain ⟨T', s'⟩ := c'
    rcases he with rfl | rfl | rfl
    · obtain ⟨vs, c, -, -, rfl⟩ := cc_op_step hs
      exact R4.post (Or.inr (Or.inl rfl))
    · obtain ⟨vs, c, -, -, rfl⟩ := cc_op_step hs
      exact R4.post (Or.inr (Or.inr rfl))
    · simp only [NT₄.cc] at hs; cases hs

theorem R4_steps {p₁ p₂ q : Int} {l : Nat} {f₁ f₂ g₀ : Int → Int} {ρ₀ : String → Const₄} (hr₁ : InR f₁ p₁)
    (hr₂ : InR f₂ p₂) {c c' : Config₄} (h : Steps₄ c c') (hr : R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ c) :
    R4 p₁ p₂ q l f₁ f₂ g₀ ρ₀ c' := by
  induction h with
  | refl => exact hr
  | step hs _ ih => exact ih (R4_step hr₁ hr₂ hr hs)

/-! ## The initial configuration: N4 closed at w₂ = ⟨p₂⟩, w₁ = ⟨p₁⟩, ℓb = ⟨l⟩ (its free variables #0, #1, #2). -/

def closeN4 (p₁ p₂ : Int) (l : Nat) : Tm₄ := ((N4.subst 0 (capv p₂)).subst 0 (capv p₁)).subst 0 (lockv l)

def ρN4 (p₁ p₂ : Int) (l : Nat) : String → Const₄ :=
  Function.update (Function.update (Function.update (fun _ => .c2 .unit) "w2" (.c2 (.cap p₂))) "w1" (.c2 (.cap p₁)))
    "lb" (.lockv l)

theorem closeN4_eq (p₁ p₂ : Int) (l : Nat) : closeN4 p₁ p₂ l = N4n.cc (ρN4 p₁ p₂ l) [] := by
  have h0 : N4 = N4n.cc (fun _ => .c2 .unit) ["w2", "w1", "lb"] :=
    NT₄.c_eq_cc _ N4n _ (by simp [N4n, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.fvIn, NA.fvIn, add, sub, mul, le, lt, eq, conj])
  have e1 := NT₄.cc_subst (fun _ => .c2 .unit) "w2" (.c2 (.cap p₂)) ["w1", "lb"] (by simp) N4n []
  have e2 := NT₄.cc_subst (Function.update (fun _ => .c2 .unit) "w2" (.c2 (.cap p₂))) "w1" (.c2 (.cap p₁)) ["lb"]
    (by simp) N4n []
  have e3 := NT₄.cc_subst (Function.update (Function.update (fun _ => .c2 .unit) "w2" (.c2 (.cap p₂))) "w1" (.c2 (.cap p₁)))
    "lb" (.lockv l) [] (by simp) N4n []
  simp only [List.nil_append, List.length_nil] at e1 e2 e3
  unfold closeN4 ρN4
  rw [h0]
  simp only [capv, lockv]
  rw [e1, e2, e3]

theorem cc_par (ρ : String → Const₄) (Γ : List String) (x₁ x₂ : String) (τ₁ τ₂ : Ty₄) (e₁ e₂ e : NT₄) :
    (NT₄.par x₁ x₂ τ₁ τ₂ e₁ e₂ e).cc ρ Γ = .par τ₁ τ₂ (e₁.cc ρ Γ) (e₂.cc ρ Γ) (e.cc ρ (x₂ :: x₁ :: Γ)) := rfl

theorem thread0 {w : String} (hw : WName w) (p₁ p₂ : Int) (l : Nat) (q : Int) (f : Int → Int) (pw : Int)
    (hpw : ρN4 p₁ p₂ l w = .c2 (.cap pw)) :
    (Fn₄ w).cc (ρN4 p₁ p₂ l) [] = (sF0 w).cc (Env w pw l q f 0) [] := by
  refine NT₄.cc_congr (S := fun x => x = w ∨ x = "lb") ?_ (Fn₄ w) [] ?_
  · rintro y (rfl | rfl)
    · rw [hpw, Env_w hw]
    · simp [ρN4, Env]
  · rcases hw with rfl | rfl <;>
      simp [Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.fvIn, NA.fvIn, add, sub, mul, le, lt, eq, conj]

theorem R4_init {p₁ p₂ q : Int} {l : Nat} {f₁ f₂ g₀ : Int → Int} {σ₁ σ₂ σb σF : Store} {L : List LockSt}
    (h1 : RegionAt p₁ 83 f₁ σ₁) (h2 : RegionAt p₂ 83 f₂ σ₂) (hb : RegionAt q 4 g₀ σb)
    (hg : ∀ s, 0 ≤ s → s < 4 → 0 ≤ g₀ (q + s))
    (D1 : Store.Disj σ₁ (σb ⊎ (σ₂ ⊎ σF))) (D2 : Store.Disj σb (σ₂ ⊎ σF)) (D3 : Store.Disj σ₂ σF)
    (hwf : Store.WF (σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF)))) (hL : L[l]? = some (.free q)) :
    R4 p₁ p₂ q l f₁ f₂ g₀ (ρN4 p₁ p₂ l) (closeN4 p₁ p₂ l, ⟨σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF)), L⟩) := by
  rw [closeN4_eq, N4n_eq, cc_par, thread0 (Or.inl rfl) p₁ p₂ l q f₁ p₁ (by simp [ρN4]),
    thread0 (Or.inr rfl) p₁ p₂ l q f₂ p₂ (by simp [ρN4])]
  exact R4.par Th.f0 Th.f0 h1 h2 hb D1 D2 D3 hwf (by simpa using hL) (by simp)
    (fun s a b => ⟨hg s a b, by simp [cnt]⟩) (fun _ h => by simp at h) (fun _ h => by simp at h)

/-- **N4-V (run_tokens₄, OBJECT-L4 H5 (a); DECLARATIONS addendum 5).** From N4 closed at its two worlds and ℓb, over a store
  holding world 1 (83 cells, f₁), the bucket region (g₀, every bucket ≥ 0), world 2 (f₂) and any frame, with ℓb free over the
  bucket region and each frame's sender and topic in range: at EVERY ⟶₄*-reachable configuration whose two `par` sides are `ret`
  (the configuration the join steps from), each world holds `postF₄` for the token its thread read, and for every sender s the emits
  naming s across both threads number at most s's initial tokens g₀(q + s). -/
theorem N4_V {p₁ p₂ q : Int} {l : Nat} {f₁ f₂ g₀ : Int → Int} {σ₁ σ₂ σb σF : Store} {L : List LockSt}
    (hr₁ : InR f₁ p₁) (hr₂ : InR f₂ p₂)
    (h1 : RegionAt p₁ 83 f₁ σ₁) (h2 : RegionAt p₂ 83 f₂ σ₂) (hb : RegionAt q 4 g₀ σb)
    (hg : ∀ s, 0 ≤ s → s < 4 → 0 ≤ g₀ (q + s))
    (D1 : Store.Disj σ₁ (σb ⊎ (σ₂ ⊎ σF))) (D2 : Store.Disj σb (σ₂ ⊎ σF)) (D3 : Store.Disj σ₂ σF)
    (hwf : Store.WF (σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF)))) (hL : L[l]? = some (.free q)) :
    ∀ c, Steps₄ (closeN4 p₁ p₂ l, ⟨σ₁ ⊎ (σb ⊎ (σ₂ ⊎ σF)), L⟩) c →
      ∀ a₁ a₂ e, c.1 = .par t4cap t4cap (.ret a₁) (.ret a₂) e →
      ∃ t₁ t₂ σ₁' σ₂' σb' σF', c.2.σ = σ₁' ⊎ (σb' ⊎ (σ₂' ⊎ σF')) ∧
        RegionAt p₁ 83 (postF₄ f₁ p₁ t₁) σ₁' ∧ RegionAt p₂ 83 (postF₄ f₂ p₂ t₂) σ₂' ∧
        ∀ s, 0 ≤ s → s < 4 →
          (if EmitsT f₁ p₁ t₁ ∧ SvA f₁ p₁ = s then (1 : Int) else 0) +
            (if EmitsT f₂ p₂ t₂ ∧ SvA f₂ p₂ = s then 1 else 0) ≤ g₀ (q + s) := by
  intro c hc a₁ a₂ e he
  have hr := R4_steps hr₁ hr₂ hc (R4_init h1 h2 hb hg D1 D2 D3 hwf hL)
  cases hr with
  | @par T₁ T₂ fc₁ fc₂ g h₁ h₂ d₁ d₂ tr₁ tr₂ σ₁' σ₂' σb' σF' L' hT₁ hT₂ hR1 hR2 hRb _ _ _ _ _ _ hcnt _ _ =>
    simp only [Tm₄.par.injEq] at he
    obtain ⟨-, -, e1, e2, -⟩ := he
    obtain ⟨⟨t₁, rfl, hd₁, -⟩, -⟩ := th_ret hT₁ e1
    obtain ⟨⟨t₂, rfl, hd₂, -⟩, -⟩ := th_ret hT₂ e2
    refine ⟨t₁, t₂, σ₁', σ₂', σb', σF', rfl, hR1, hR2, fun s a b => ?_⟩
    obtain ⟨hg0, hsum⟩ := hcnt s a b
    simp only [cnt, hd₁, hd₂] at hsum
    omega
  | @post ρ s e' he' =>
    rcases he' with rfl | rfl | rfl <;> simp [NT₄.cc, BN] at he

end VIRL4
