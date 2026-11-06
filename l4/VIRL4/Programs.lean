/-
  O95 layer L4, Lean arm (amend-21). The programs N1–N3 as de Bruijn Tm₄, read under errata L4-E1 (par binds its two results)
  and L4-E2 (N1 releases c2; INC ends `let u ← release in ret u`; N3's fixed term). N2 is "N1 with newlock removed and both sides
  given c1 directly" (inputs §3): each side loads and stores c1 itself and returns it. Its refutation is the typing row.
  Each derivation is built by `l4ty`, which applies ⊢₄'s rules syntax-directed.
-/
import VIRL4.Typing4
import VIRL4.Rules4

namespace VIRL4
open VIRL1 VIRL2 VIRL3

abbrev c4 (n : Int) : Atom₄ := .const (.c2 (.int n))
abbrev v4 (n : Nat) : Atom₄ := .var n
def padd (a b : Atom₄) : Atom₄ := .prim .add [a, b]

/-- INC ℓ, with ℓ at index k: `let d ← acquire(ℓ) in let y ← load(d,0) in let d1 ← store(d,0,add(y,1)) in let u ← release(ℓ,d1) in ret u`. -/
def INC (k : Nat) : Tm₄ :=
  .letOp .acquire [v4 k] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .letOp .release [v4 (k + 3), v4 0] t4unit <|
  .ret (v4 0)

/-- N1 (L4-E1, L4-E2): alloc · store 0 · newlock · par (INC) (INC) · acquire · load · release · ret x. -/
def N1 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .letOp .newlock [v4 0] t4lock <|
  .par t4unit t4unit (INC 0) (INC 0) <|
  .letOp .acquire [v4 2] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp .release [v4 4, v4 1] t4unit <|
  .ret (v4 1)

/-- N2's side: c1 at index 0, used directly (no lock): load, store, return the capability. -/
def SIDE : Tm₄ :=
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .ret (v4 0)

/-- N2: N1 with newlock removed, both sides given c1; the body frees both results. -/
def N2 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .par t4cap t4cap SIDE SIDE <|
  .letOp (.o2 .free) [v4 0] t4unit <|
  .letOp (.o2 .free) [v4 2] t4unit <|
  .ret (c4 0)

/-- N3 (L4-E2): a release whose cell holds −1 under inv(v) := v ≥ 0. -/
def N3 : Tm₄ :=
  .letOp (.o2 .alloc) [c4 1] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 0] t4cap <|
  .letOp .newlock [v4 0] t4lock <|
  .letOp .acquire [v4 0] t4cap <|
  .letOp (.o2 .store) [v4 0, c4 0, c4 (-1)] t4cap <|
  .letOp .release [v4 2, v4 0] t4unit <|
  .ret (v4 0)

theorem split_none_all : ∀ Δ : List Bool, (∀ b ∈ Δ, b = false) → Split Δ Δ Δ
  | [], _ => .nil
  | b :: Δ, h => by
      have hb := h b (by simp); subst hb
      exact .none (split_none_all Δ (fun x hx => h x (by simp [hx])))

/-- `par` is applied only where every capability is already consumed (all-`none` splits), which is N1's case. -/
macro "l4ty" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl
  | exact HasTypeA₄.int | exact HasTypeA₄.bool | exact HasTypeA₄.unit
  | exact HasTypeA₄.var rfl rfl
  | refine HasTypeA₄.prim ?_
  | exact HasTypeL₄.nil | refine HasTypeL₄.cons ?_ ?_
  | refine HasType₄.ret ?_ ?_
  | refine HasType₄.alloc ?_ ?_
  | refine HasType₄.load rfl rfl ?_ ?_
  | refine HasType₄.store rfl rfl ?_ ?_ ?_
  | refine HasType₄.free rfl rfl ?_
  | refine HasType₄.newlock rfl rfl ?_
  | refine HasType₄.acquire ?_ ?_
  | refine HasType₄.release ?_ rfl rfl ?_
  | refine HasType₄.par (split_none_all _ (by decide)) (split_none_all _ (by decide)) (Or.inr rfl) (Or.inr rfl) ?_ ?_ ?_))

/-- N1-T. -/
theorem N1_typed : HasType₄ [] [] N1 t4int := by
  simp only [N1, INC, padd]
  l4ty

/-- N3-T: TYPED (⊢₄ does not read invariants). -/
theorem N3_typed : HasType₄ [] [] N3 t4unit := by
  simp only [N3]
  l4ty

/-- N2's row: ILL-TYPED at every type. Both sides open with a load of c1, so each needs c1 in its mask; the split gives it to one. -/
theorem N2_untyped : ∀ τ, ¬ HasType₄ [] [] N2 τ := by
  intro τ h
  simp only [N2, SIDE, padd] at h
  cases h with
  | alloc _ h =>
  cases h with
  | store _ _ _ _ h =>
  cases h with
  | par s₁ s₂ _ _ h₁ h₂ _ =>
  cases h₁ with
  | load _ hΔ₁ _ _ =>
  cases h₂ with
  | load _ hΔ₂ _ _ =>
  cases s₁ <;> cases s₂ <;> simp_all

/-! ## N1-S: `{emp} N1 {v. v ∈ ℤ}` (inputs/L4-programs.md §3), proved from the rules of Rules4 under the invariant I₁ "the lock's region is
  ONE cell, any contents". The VALUE 2 is N1-V, a configuration invariant on ⟶₄ (H5 (a)), not this triple. -/

def I₁ : Int → Assn := fun p σ => ∃ f, RegionAt p 1 f σ

/-- Lock l has base p (a stable lock-table fact). -/
def LB (l : Nat) (p : Int) (L : List LockSt) : Prop := (L.map LockSt.base)[l]? = some p

theorem triple₄_conseq {I : Int → Assn} {P P' : Assn₄} {e : Tm₄} {R : Atom₄ → Assn₄}
    (h : ∀ L σ, P' L σ → P L σ) (ht : Triple₄ I P e R) : Triple₄ I P' e R :=
  fun n L σ hp => ht n L σ (h L σ hp)

theorem triple₄_pre_ex {I : Int → Assn} {α : Type} {P : α → Assn₄} {e : Tm₄} {R : Atom₄ → Assn₄}
    (h : ∀ x, Triple₄ I (P x) e R) : Triple₄ I (fun L σ => ∃ x, P x L σ) e R :=
  fun n L σ ⟨x, hx⟩ => h x n L σ hx

theorem triple₄_pre_pure {I : Int → Assn} {φ : Prop} {P : Assn₄} {e : Tm₄} {R : Atom₄ → Assn₄}
    (h : φ → Triple₄ I P e R) : Triple₄ I (fun L σ => φ ∧ P L σ) e R :=
  fun n L σ ⟨hφ, hp⟩ => h hφ n L σ hp

/-- INC with its lock id substituted. -/
def INCv (l : Nat) : Tm₄ :=
  .letOp .acquire [lockv l] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp (.o2 .store) [v4 1, c4 0, padd (v4 0) (c4 1)] t4cap <|
  .letOp .release [lockv l, v4 0] t4unit <|
  .ret (v4 0)

/-- N1's last critical section, as written in N1 (before the lock is substituted) and after. -/
def TAIL0 : Tm₄ :=
  .letOp .acquire [v4 2] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp .release [v4 4, v4 1] t4unit <|
  .ret (v4 1)

def TAILv (l : Nat) : Tm₄ :=
  .letOp .acquire [lockv l] t4cap <|
  .letOp (.o2 .load) [v4 0, c4 0] t4int <|
  .letOp .release [lockv l, v4 1] t4unit <|
  .ret (v4 1)

theorem stable_emp_LB (l : Nat) (p : Int) : Stable (fun L σ => σ = Store.empty ∧ LB l p L) :=
  fun _ _ _ hx h => ⟨h.1, base_of_ext h.2 hx⟩

theorem release_split {l : Nat} {p : Int} {L : List LockSt} {σ : Store} {f : Int → Int} (hf : RegionAt p 1 f σ) :
    ∃ σ₀ σI, Store.Disj σ₀ σI ∧ σ = σ₀ ⊎ σI ∧ OwnsRegion p σI ∧ I₁ p σI ∧ σ₀ = Store.empty :=
  ⟨Store.empty, σ, disj_empty_left σ, (Store.empty_union σ).symm, ⟨1, hf.isRegion⟩, ⟨f, hf⟩, rfl⟩

/-- One INC thread: from emp (and lock l's base p), it returns with emp. -/
theorem INC_triple (p : Int) (l : Nat) :
    Triple₄ I₁ (fun L σ => σ = Store.empty ∧ LB l p L) (INCv l) (fun _ L σ => σ = Store.empty ∧ LB l p L) := by
  unfold INCv
  refine acquire₄_rule (p := p) (fun L σ h => h.2) (stable_emp_LB l p) ?_
  show Triple₄ I₁ _ (.letOp (.o2 .load) [capv p, c4 0] t4int <|
    .letOp (.o2 .store) [capv p, c4 0, padd (v4 0) (c4 1)] t4cap <| .letOp .release [lockv l, v4 0] t4unit <| .ret (v4 0)) _
  refine op₄_rule (vs := [capv p, c4 0]) (ws := [.const (.cap p), .const (.int 0)]) rfl rfl
    (Post := fun v L σ => (∃ w, v = c4 w) ∧ (∃ f, RegionAt p 1 f σ) ∧ LB l p L) ?_ ?_
  · rintro L σ' ⟨σ, σI, _, rfl, ⟨rfl, hb⟩, _, f, hf⟩
    refine ⟨RegionAt p 1 f, _, load_at p 1 f 0 (by omega), by rw [Store.empty_union]; exact hf, ?_⟩
    rintro v σq ⟨rfl, hq⟩
    exact ⟨⟨f (p + 0), rfl⟩, ⟨f, hq⟩, hb⟩
  · intro v
    apply triple₄_pre_pure
    rintro ⟨w, rfl⟩
    show Triple₄ I₁ _ (.letOp (.o2 .store) [capv p, c4 0, padd (c4 w) (c4 1)] t4cap <|
      .letOp .release [lockv l, v4 0] t4unit <| .ret (v4 0)) _
    refine op₄_rule (vs := [capv p, c4 0, c4 (w + 1)]) (ws := [.const (.cap p), .const (.int 0), .const (.int (w + 1))])
      rfl rfl (Post := fun v L σ => v = capv p ∧ (∃ f, RegionAt p 1 f σ) ∧ LB l p L) ?_ ?_
    · rintro L σ ⟨⟨f, hf⟩, hb⟩
      refine ⟨RegionAt p 1 f, _, store_at p 1 f 0 (w + 1) (by omega), hf, ?_⟩
      rintro v σq ⟨rfl, hq⟩
      exact ⟨rfl, ⟨_, hq⟩, hb⟩
    · intro v
      apply triple₄_pre_pure
      rintro rfl
      show Triple₄ I₁ _ (.letOp .release [lockv l, capv p] t4unit <| .ret (v4 0)) _
      refine release₄_rule (p := p) (P' := fun L σ => σ = Store.empty ∧ LB l p L) (fun L σ h => h.2) ?_
        (stable_emp_LB l p) ?_
      · rintro L σ ⟨⟨f, hf⟩, hb⟩
        obtain ⟨σ₀, σI, hd, he, ho, hi, rfl⟩ := release_split (l := l) (L := L) hf
        exact ⟨_, σI, hd, he, ho, hi, rfl, hb⟩
      · show Triple₄ I₁ _ (.ret unitv) _
        exact ret₄_rule rfl (fun L σ h L' hx => stable_emp_LB l p L L' σ hx h)

/-- N1's last critical section: acquire, load, release, return the loaded int. -/
theorem TAIL_triple (p : Int) (l : Nat) :
    Triple₄ I₁ (fun L σ => σ = Store.empty ∧ LB l p L) (TAILv l) (fun v _ _ => ∃ w, v = c4 w) := by
  unfold TAILv
  refine acquire₄_rule (p := p) (fun L σ h => h.2) (stable_emp_LB l p) ?_
  show Triple₄ I₁ _ (.letOp (.o2 .load) [capv p, c4 0] t4int <| .letOp .release [lockv l, capv p] t4unit <| .ret (v4 1)) _
  refine op₄_rule (vs := [capv p, c4 0]) (ws := [.const (.cap p), .const (.int 0)]) rfl rfl
    (Post := fun v L σ => (∃ w, v = c4 w) ∧ (∃ f, RegionAt p 1 f σ) ∧ LB l p L) ?_ ?_
  · rintro L σ' ⟨σ, σI, _, rfl, ⟨rfl, hb⟩, _, f, hf⟩
    refine ⟨RegionAt p 1 f, _, load_at p 1 f 0 (by omega), by rw [Store.empty_union]; exact hf, ?_⟩
    rintro v σq ⟨rfl, hq⟩
    exact ⟨⟨f (p + 0), rfl⟩, ⟨f, hq⟩, hb⟩
  · intro v
    apply triple₄_pre_pure
    rintro ⟨w, rfl⟩
    show Triple₄ I₁ _ (.letOp .release [lockv l, capv p] t4unit <| .ret (c4 w)) _
    refine release₄_rule (p := p) (P' := fun _ _ => True) (fun L σ h => h.2) ?_ (fun _ _ _ _ _ => trivial) ?_
    · rintro L σ ⟨⟨f, hf⟩, _⟩
      obtain ⟨σ₀, σI, hd, he, ho, hi, rfl⟩ := release_split (l := l) (L := L) hf
      exact ⟨_, σI, hd, he, ho, hi, trivial⟩
    · show Triple₄ I₁ _ (.ret (c4 w)) _
      exact ret₄_rule rfl (fun _ _ _ _ _ => ⟨w, rfl⟩)

/-- N1-S: `{emp} N1 {v. v ∈ ℤ}`. -/
theorem N1_S : Triple₄ I₁ (fun _ σ => σ = Store.empty) N1 (fun v _ _ => ∃ w, v = c4 w) := by
  unfold N1
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
    show Triple₄ I₁ _ (.letOp (.o2 .store) [capv p, c4 0, c4 0] t4cap <| .letOp .newlock [v4 0] t4lock <|
      .par t4unit t4unit (INC 0) (INC 0) TAIL0) _
    refine op₄_rule (vs := [capv p, c4 0, c4 0]) (ws := [.const (.cap p), .const (.int 0), .const (.int 0)]) rfl rfl
      (Post := fun v _ σ => v = capv p ∧ ∃ f, RegionAt p 1 f σ) ?_ ?_
    · intro L σ h
      refine ⟨_, _, store_at p 1 (fun _ => 0) 0 0 (by omega), h, ?_⟩
      rintro v σq ⟨rfl, hq⟩
      exact ⟨rfl, _, hq⟩
    · intro v
      apply triple₄_pre_pure
      rintro rfl
      show Triple₄ I₁ _ (.letOp .newlock [capv p] t4lock <| .par t4unit t4unit (INC 0) (INC 0) TAIL0) _
      refine newlock₄_rule (p := p) (P' := fun _ σ => σ = Store.empty) ?_ (fun _ _ _ _ h => h) (fun k => ?_)
      · rintro L σ ⟨f, hf⟩
        exact release_split (l := 0) (L := L) hf
      · show Triple₄ I₁ _ (.par t4unit t4unit (INCv k) (INCv k) (TAILv k)) _
        refine triple₄_conseq (P := sep₄ (fun L σ => σ = Store.empty ∧ LB k p L) (fun L σ => σ = Store.empty ∧ LB k p L))
          ?_ (par₄_rule (INC_triple p k) (INC_triple p k) (fun v₁ v₂ => ?_))
        · rintro L σ ⟨rfl, hb⟩
          exact ⟨Store.empty, Store.empty, disj_empty_left _, (Store.empty_union _).symm, ⟨rfl, hb⟩, ⟨rfl, hb⟩⟩
        · show Triple₄ I₁ _ (TAILv k) _
          refine triple₄_conseq ?_ (TAIL_triple p k)
          rintro L σ ⟨σ₁, σ₂, _, rfl, ⟨rfl, hb⟩, ⟨rfl, _⟩⟩
          exact ⟨Store.empty_union _, hb⟩

end VIRL4
