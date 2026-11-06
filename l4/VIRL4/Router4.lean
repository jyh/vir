/-
  O95 layer L4, Lean arm (amend-21; H4 (a); erratum L4-E2 part (4), errata/L4-E2-N4.md). N4's terms: F₄ (L3's F with ONE critical
  section on the bucket region `b` behind the lock ℓb) and the two-router program `par (F₄[w₁]) (F₄[w₂])`, written with NAMES as
  L3 wrote F and compiled to de Bruijn `Tm₄` by `NT₄.c` (L3's named atoms `NA` reused through ι). N4-T: both typed by ⊢₄.
  Rows still owed on N4: N4-S (each side's triple) and N4-V (run_tokens₄ as a configuration invariant).
-/
import VIRL4.NoRace

namespace VIRL4
open VIRL1 VIRL2 VIRL3

/-- Named L4 terms: L3's forms plus `par` (two binders) and `ret ()`. -/
inductive NT₄ where
  | ret (a : NA)
  | retU
  | letE (x : String) (τ : Ty₄) (e₁ e₂ : NT₄)
  | op (x : String) (τ : Ty₄) (o : Op₄) (as : List NA) (e : NT₄)
  | ite (a : NA) (e₁ e₂ : NT₄)
  | par (x₁ x₂ : String) (τ₁ τ₂ : Ty₄) (e₁ e₂ e : NT₄)

def NA.c₄ (Γ : List String) (a : NA) : Atom₄ := ιA (a.c Γ)

/-- Compile in scope Γ (innermost first); `par` binds x₁ = #1, x₂ = #0 in its body (erratum L4-E1). -/
def NT₄.c (Γ : List String) : NT₄ → Tm₄
  | .ret a => .ret (NA.c₄ Γ a)
  | .retU => .ret unitv
  | .letE x τ e₁ e₂ => .letE τ (e₁.c Γ) (e₂.c (x :: Γ))
  | .op x τ o as e => .letOp o (as.map (NA.c₄ Γ)) τ (e.c (x :: Γ))
  | .ite a e₁ e₂ => .ite (NA.c₄ Γ a) (e₁.c Γ) (e₂.c Γ)
  | .par x₁ x₂ τ₁ τ₂ e₁ e₂ e => .par τ₁ τ₂ (e₁.c Γ) (e₂.c Γ) (e.c (x₂ :: x₁ :: Γ))

/-! The macros, as L3's (inputs/L3-programs.md), over NT₄. -/
def RD32₄ (w : String) (o : Int) (x : String) (k : NT₄) : NT₄ :=
  let x0 := x ++ "0"; let x1 := x ++ "1"; let x2 := x ++ "2"; let x3 := x ++ "3"
  .op x0 t4int (.o2 .load) [.v w, .i (3 + o)] <|
  .op x1 t4int (.o2 .load) [.v w, .i (4 + o)] <|
  .op x2 t4int (.o2 .load) [.v w, .i (5 + o)] <|
  .op x3 t4int (.o2 .load) [.v w, .i (6 + o)] <|
  .letE x t4int (.ret (add (.v x0) (add (mul (.i 256) (.v x1))
      (add (mul (.i 65536) (.v x2)) (mul (.i 16777216) (.v x3)))))) k

def EXIT₄ (w : String) (c : Int) : NT₄ :=
  .op "w'" t4cap (.o2 .store) [.v w, .i 1, .i c] (.ret (.v "w'"))

def EMIT₄ (w : String) : NT₄ :=
  .op "w'" t4cap (.o2 .store) [.v w, .i 1, .i 0] <|
  .op "w''" t4cap (.o2 .store) [.v "w'", .i 2, .i 24] (.ret (.v "w''"))

/-- F₄ on the world named w, with the lock named "lb" (errata/L4-E2-N4.md, "F₄"). -/
def Fn₄ (w : String) : NT₄ :=
  .op "n" t4int (.o2 .load) [.v w, .i 0] <|
  .ite (le (.i 24) (.v "n"))
    (RD32₄ w 0 "magic" <| RD32₄ w 4 "sender" <| RD32₄ w 8 "topic" <|
      .op "a" t4int (.o2 .load) [.v w, add (.i A) (add (mul (.v "sender") (.i NTp)) (.v "topic"))] <|
      .op "b" t4cap .acquire [.v "lb"] <|
      .op "t" t4int (.o2 .load) [.v "b", .v "sender"] <|
      .ite (conj (eq (.v "magic") (.i MAGIC)) (conj (eq (.v "a") (.i 1)) (lt (.i 0) (.v "t"))))
        (.op "b1" t4cap (.o2 .store) [.v "b", .v "sender", sub (.v "t") (.i 1)] <|
          .op "r" t4unit .release [.v "lb", .v "b1"] (EMIT₄ w))
        (.op "r" t4unit .release [.v "lb", .v "b"] (EXIT₄ w 2)))
    (EXIT₄ w 1)

/-- F₄ alone: free variables w : cap (#0), ℓb : lock (#1). -/
def F₄ : Tm₄ := (Fn₄ "w").c ["w", "lb"]

/-- N4 (errata/L4-E2-N4.md): free variables w₂ (#0), w₁ (#1), ℓb (#2). -/
def N4n : NT₄ :=
  .par "w1'" "w2'" t4cap t4cap (Fn₄ "w1") (Fn₄ "w2") <|
  .op "u1" t4unit (.o2 .free) [.v "w1'"] <|
  .op "u2" t4unit (.o2 .free) [.v "w2'"] .retU

def N4 : Tm₄ := N4n.c ["w2", "w1", "lb"]

theorem mask_only_zero {Δ : List Bool} (h : Mask.empty Δ) : Mask.only (true :: Δ) 0 :=
  ⟨rfl, fun m hm => by
    cases m with
    | zero => exact absurd rfl hm
    | succ m => simpa using h m⟩

/-- ⊢₄ syntax-directed, for terms whose `let`s bind pure values (RD32's sum) and whose exits return the world. -/
macro "l4ty'" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl | exact Or.inl rfl
  | exact HasTypeA₄.int | exact HasTypeA₄.bool | exact HasTypeA₄.unit
  | exact HasTypeA₄.var rfl rfl
  | refine HasTypeA₄.prim ?_
  | exact HasTypeL₄.nil | refine HasTypeL₄.cons ?_ ?_
  | refine HasType₄.retCap rfl (mask_only_zero ?_)
  | refine HasType₄.ret ?_ ?_
  | refine HasType₄.letE (split_left_empty _) (Or.inr rfl) ?_ ?_
  | refine HasType₄.ite ?_ ?_ ?_
  | refine HasType₄.load rfl rfl ?_ ?_
  | refine HasType₄.store rfl rfl ?_ ?_ ?_
  | refine HasType₄.free rfl rfl ?_
  | refine HasType₄.acquire ?_ ?_
  | refine HasType₄.release ?_ rfl rfl ?_))

set_option maxRecDepth 4000 in
/-- N4-T, F₄'s half: F₄ is typed `cap` in (w : cap, ℓb : lock) with Δ = {w}. -/
theorem F₄_typed : HasType₄ [t4cap, t4lock] [true, false] F₄ t4cap := by
  simp only [F₄, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.c, NA.c₄, NA.c, ιA, ιL, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
  l4ty'

set_option maxRecDepth 4000 in
/-- N4-T: N4 is typed `unit` in (w₂ : cap, w₁ : cap, ℓb : lock) with Δ = {w₁, w₂}: par gives w₁ to the left side, w₂ to the right,
  nothing to the body, which frees the two returned worlds. -/
theorem N4_typed : HasType₄ [t4cap, t4cap, t4lock] [true, true, false] N4 t4unit := by
  simp only [N4, N4n, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.c, NA.c₄, NA.c, ιA, ιL, add, sub, mul, le, lt, eq, conj, List.map,
    List.idxOf, List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd,
    Nat.zero_add]
  refine HasType₄.par (Δ₁ := [false, true, false]) (Δ' := [true, false, false]) (Δ₂ := [true, false, false])
    (Δ₀ := [false, false, false]) (Split.right (Split.left (Split.none Split.nil))) (Split.left (Split.none (Split.none Split.nil)))
    (Or.inl rfl) (Or.inl rfl) ?_ ?_ ?_ <;> l4ty'

/-! ## N4-S's machinery: L2's region axioms at L4 with a frame Fr beside the region and a lock-table fact Rest. -/

def StableR (Rest : List LockSt → Prop) : Prop := ∀ L L', Ext L L' → Rest L → Rest L'

theorem stable_and {X : Assn} {Rest : List LockSt → Prop} (hR : StableR Rest) : Stable (fun L σ => X σ ∧ Rest L) :=
  fun L L' _ hx h => ⟨h.1, hR L L' hx h.2⟩

theorem load₄_at {I : Int → Assn} {Fr : Assn} {Rest : List LockSt → Prop} {p : Int} {n : Nat} {f : Int → Int}
    {ai : Atom₄} {i : Int} (hai : Atom₄.eval ai = some (c4 i)) (hi : 0 ≤ i ∧ i < n) {τ : Ty₄} {e : Tm₄}
    {Q : Atom₄ → Assn₄}
    (hk : Triple₄ I (fun L σ => (RegionAt p n f ∗ Fr) σ ∧ Rest L) (e.subst 0 (c4 (f (p + i)))) Q) :
    Triple₄ I (fun L σ => (RegionAt p n f ∗ Fr) σ ∧ Rest L) (.letOp (.o2 .load) [capv p, ai] τ e) Q := by
  refine op₄_rule (vs := [capv p, c4 i]) (ws := [.const (.cap p), .const (.int i)])
    (by simp [Atom₄.evalL, Atom₄.eval, capv, hai]) rfl
    (Post := fun v L σ => v = c4 (f (p + i)) ∧ ((RegionAt p n f ∗ Fr) σ ∧ Rest L)) ?_ ?_
  · rintro L σ ⟨h, hr⟩
    refine ⟨_, _, op_frame Fr (load_at p n f i hi), h, ?_⟩
    rintro v σq hq
    obtain ⟨hv, hq'⟩ := sep_pure_left hq
    exact ⟨by rw [hv]; rfl, hq', hr⟩
  · intro v
    apply triple₄_pre_pure
    rintro rfl
    exact hk

theorem store₄_at {I : Int → Assn} {Fr : Assn} {Rest : List LockSt → Prop} {p : Int} {n : Nat} {f : Int → Int}
    {ai av : Atom₄} {i v : Int} (hai : Atom₄.eval ai = some (c4 i)) (hav : Atom₄.eval av = some (c4 v))
    (hi : 0 ≤ i ∧ i < n) {τ : Ty₄} {e : Tm₄} {Q : Atom₄ → Assn₄}
    (hk : Triple₄ I (fun L σ => (RegionAt p n (Function.update f (p + i) v) ∗ Fr) σ ∧ Rest L) (e.subst 0 (capv p)) Q) :
    Triple₄ I (fun L σ => (RegionAt p n f ∗ Fr) σ ∧ Rest L) (.letOp (.o2 .store) [capv p, ai, av] τ e) Q := by
  refine op₄_rule (vs := [capv p, c4 i, c4 v]) (ws := [.const (.cap p), .const (.int i), .const (.int v)])
    (by simp [Atom₄.evalL, Atom₄.eval, capv, hai, hav]) rfl
    (Post := fun c L σ => c = capv p ∧ ((RegionAt p n (Function.update f (p + i) v) ∗ Fr) σ ∧ Rest L)) ?_ ?_
  · rintro L σ ⟨h, hr⟩
    refine ⟨_, _, op_frame Fr (store_at p n f i v hi), h, ?_⟩
    rintro c σq hq
    obtain ⟨hc, hq'⟩ := sep_pure_left hq
    exact ⟨by rw [hc]; rfl, hq', hr⟩
  · intro c
    apply triple₄_pre_pure
    rintro rfl
    exact hk

theorem sep_emp_right' {P : Assn} {σ : Store} (h : (P ∗ Assn.emp) σ) : P σ := by
  obtain ⟨σ₁, σ₂, _, rfl, hp, rfl⟩ := h
  rw [store_empty_union_right]; exact hp

theorem sep_emp_right_intro {P : Assn} {σ : Store} (h : P σ) : (P ∗ Assn.emp) σ :=
  ⟨σ, Store.empty, disj_symm (disj_empty_left σ), (store_empty_union_right σ).symm, h, rfl⟩

/-- N4-S's world post-state: L3's `postF` without the bucket write, the token t read inside the critical section. -/
def postF₄ (f : Int → Int) (p t : Int) : Int → Int :=
  if 24 ≤ f (p + 0) then
    if MgA f p = MAGIC ∧ f (aclA f p) = 1 ∧ 0 < t then Function.update (Function.update f (p + 1) 0) (p + 2) 24
    else Function.update f (p + 1) 2
  else Function.update f (p + 1) 1

/-- ℓb's invariant (errata/L4-E2-N4.md): every bucket is non-negative. -/
def Ib : Int → Assn := fun q σ => ∃ g : Int → Int, (∀ s, 0 ≤ s → s < 4 → 0 ≤ g (q + s)) ∧ RegionAt q 4 g σ

/-- A thread's F₄ with its world ⟨p⟩ and its lock ⟨l⟩ substituted. -/
def closeAt₄ (p : Int) (l : Nat) (e : Tm₄) : Tm₄ := (e.subst 0 (capv p)).subst 0 (lockv l)

macro "n4s" : tactic => `(tactic| try simp only [lockv, capv, Tm₄.subst, Atom₄.subst, Atom₄.substL, ↓reduceIte, Nat.reduceAdd,
  Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd])
/-- One load from a region at a constant index. -/
macro "ld4" : tactic => `(tactic| (refine load₄_at rfl ?_ ?_; (first | omega | (simp only [A, K, NW, NS, NTp, SvA, TvA, MgA] at *; omega)); n4s))
/-- One store into a region at constant index and value. -/
macro "st4" : tactic => `(tactic| (refine store₄_at rfl rfl ?_ ?_; (first | omega | (simp only [A, K, NW, NS, NTp, SvA, TvA, MgA] at *; omega)); n4s))
macro "ev4" : tactic => `(tactic| simp [Atom₄.eval, Atom₄.evalL, constsOf₄, Const₄.toL1, Const.toL1, L1.Prim.interp, Const.ofL1,
  Const₄.toBool, MgA, SvA, TvA, A, NW, NTp])

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- N4-S, one side: from its world (83 cells at p) and lock l's base q, F₄ keeps ℓb's invariant (it releases the bucket region
  with every bucket ≥ 0 on both paths) and returns its world with L3's out cells written, for the token t it read. -/
theorem F₄_S {p q : Int} {l : Nat} {f : Int → Int} (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p)
    (ht4 : TvA f p < 4) :
    Triple₄ Ib (fun L σ => (RegionAt p 83 f ∗ Assn.emp) σ ∧ LB l q L) (closeAt₄ p l F₄)
      (fun v _ σ => v = capv p ∧ ∃ t, RegionAt p 83 (postF₄ f p t) σ) := by
  have hLB : StableR (LB l q) := fun _ _ hx h => base_of_ext h hx
  simp only [closeAt₄, F₄, Fn₄, RD32₄, EXIT₄, EMIT₄, NT₄.c, NA.c₄, NA.c, ιA, ιL, add, sub, mul, le, lt, eq, conj, List.map,
    List.idxOf, List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd,
    Nat.zero_add, lockv, capv, Tm₄.subst, Atom₄.subst, Atom₄.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  ld4
  by_cases hn : 24 ≤ f (p + 0)
  · refine ite₄_rule (c := .c2 (.bool true)) (b := true) (by ev4; simpa using hn) rfl (stable_and hLB) ?_
    n4s
    ld4; ld4; ld4; ld4
    refine letRet₄_rule (v := c4 (MgA f p)) (by ev4) (stable_and hLB) ?_; n4s
    ld4; ld4; ld4; ld4
    refine letRet₄_rule (v := c4 (SvA f p)) (by ev4) (stable_and hLB) ?_; n4s
    ld4; ld4; ld4; ld4
    refine letRet₄_rule (v := c4 (TvA f p)) (by ev4) (stable_and hLB) ?_; n4s
    refine load₄_at (i := 67 + (SvA f p * 4 + TvA f p)) (by ev4) (by simp only [SvA, TvA] at *; omega) ?_; n4s
    refine acquire₄_rule (p := q) (fun L σ h => h.2) (stable_and hLB) ?_; n4s
    refine triple₄_conseq (P := fun L σ' => ∃ g : Int → Int, (∀ s, 0 ≤ s → s < 4 → 0 ≤ g (q + s)) ∧
      ((RegionAt q 4 g ∗ (RegionAt p 83 f ∗ Assn.emp)) σ' ∧ LB l q L)) ?_ ?_
    · rintro L σ' ⟨σ, σI, hd, rfl, ⟨hw, hb⟩, _, g, hg, hgr⟩
      exact ⟨g, hg, ⟨σI, σ, disj_symm hd, union_comm_disj hd, hgr, hw⟩, hb⟩
    apply triple₄_pre_ex
    intro g
    apply triple₄_pre_pure
    intro hg
    refine load₄_at (i := SvA f p) rfl (by omega) ?_; n4s
    by_cases he : MgA f p = MAGIC ∧ f (p + (67 + (SvA f p * 4 + TvA f p))) = 1 ∧ 0 < g (q + SvA f p)
    · refine ite₄_rule (c := .c2 (.bool true)) (b := true) (by ev4; exact he) rfl (stable_and hLB) ?_
      n4s
      refine store₄_at (i := SvA f p) (v := g (q + SvA f p) - 1) rfl (by ev4) (by omega) ?_; n4s
      refine release₄_rule (p := q) (P' := fun L σ => (RegionAt p 83 f ∗ Assn.emp) σ ∧ LB l q L) (fun L σ h => h.2) ?_
        (stable_and hLB) ?_
      · rintro L σ ⟨⟨σb, σw, hd, rfl, hbr, hw⟩, hb⟩
        refine ⟨σw, σb, disj_symm hd, union_comm_disj hd, ⟨4, hbr.isRegion⟩, ⟨_, ?_, hbr⟩, hw, hb⟩
        intro s hs0' hs4'
        by_cases hsq : q + s = q + SvA f p
        · rw [hsq, Function.update_self]; omega
        · rw [Function.update_of_ne hsq]; exact hg s hs0' hs4'
      n4s
      st4; st4
      refine ret₄_rule rfl (fun L σ h L' _ => ⟨rfl, g (q + SvA f p), ?_⟩)
      have hw := sep_emp_right' h.1
      have hn' : 24 ≤ f p := by simpa using hn
      simpa [postF₄, hn', aclA, he] using hw
    · refine ite₄_rule (c := .c2 (.bool false)) (b := false) (by ev4; intro h1 h2; by_contra h3; exact he ⟨h1, h2, not_le.1 h3⟩) rfl (stable_and hLB) ?_
      n4s
      refine release₄_rule (p := q) (P' := fun L σ => (RegionAt p 83 f ∗ Assn.emp) σ ∧ LB l q L) (fun L σ h => h.2) ?_
        (stable_and hLB) ?_
      · rintro L σ ⟨⟨σb, σw, hd, rfl, hbr, hw⟩, hb⟩
        exact ⟨σw, σb, disj_symm hd, union_comm_disj hd, ⟨4, hbr.isRegion⟩, ⟨g, hg, hbr⟩, hw, hb⟩
      n4s
      st4
      refine ret₄_rule rfl (fun L σ h L' _ => ⟨rfl, g (q + SvA f p), ?_⟩)
      have hw := sep_emp_right' h.1
      have hn' : 24 ≤ f p := by simpa using hn
      simpa [postF₄, hn', aclA, he] using hw
  · refine ite₄_rule (c := .c2 (.bool false)) (b := false) (by ev4; simpa using hn) rfl (stable_and hLB) ?_
    n4s
    st4
    refine ret₄_rule rfl (fun L σ h L' _ => ⟨rfl, 0, ?_⟩)
    have hw := sep_emp_right' h.1
    have hn' : ¬ 24 ≤ f p := by simpa using hn
    simpa [postF₄, hn'] using hw

end VIRL4
