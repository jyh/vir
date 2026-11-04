/-
  O95 layer L2, Lean arm. OBJECT-L2 §5: the program logic. Assertions are predicates on store FRAGMENTS; ∗ is disjoint
  union in both components; the triple is SEMANTIC, defined from ⟶₂ (l2/DECLARATIONS-LEAN.md): partial correctness and NO
  FAULT, from the fragment together with ANY disjoint frame. The frame rule is proved from that definition for EVERY L2
  program, with no hypothesis about the regions it does not touch, and mentions no ⊢₂ judgement (amend-16 Y3, Y4).
-/
import VIRL2.Typing2

namespace VIRL2
open VIRL1

namespace Store

/-- Two fragments are disjoint in both components. -/
def Disj (σ₁ σ₂ : Store) : Prop := σ₁.H.Disjoint σ₂.H ∧ σ₁.R.Disjoint σ₂.R

/-- Their union. -/
def union (σ₁ σ₂ : Store) : Store := ⟨σ₁.H ∪ σ₂.H, σ₁.R ∪ σ₂.R⟩

infixl:65 " ⊎ " => Store.union

theorem union_assoc (σ₁ σ₂ σ₃ : Store) : σ₁ ⊎ σ₂ ⊎ σ₃ = σ₁ ⊎ (σ₂ ⊎ σ₃) := by
  simp [union, Finmap.union_assoc]

theorem disj_union_left (x y z : Store) : Disj (x ⊎ y) z ↔ Disj x z ∧ Disj y z := by
  simp only [Disj, union, Finmap.disjoint_union_left]; tauto

theorem disj_union_right (x y z : Store) : Disj x (y ⊎ z) ↔ Disj x y ∧ Disj x z := by
  simp only [Disj, union, Finmap.disjoint_union_right]; tauto

end Store

/-- Assertions over store fragments. -/
abbrev Assn := Store → Prop

namespace Assn
def emp : Assn := fun σ => σ = Store.empty
def sep (P Q : Assn) : Assn := fun σ => ∃ σ₁ σ₂, Store.Disj σ₁ σ₂ ∧ σ = σ₁ ⊎ σ₂ ∧ P σ₁ ∧ Q σ₂
def pure (φ : Prop) : Assn := fun σ => φ ∧ σ = Store.empty
/-- `p ↦ v`: exactly the one cell. -/
def pt (p v : Int) : Assn := fun σ => σ = ⟨Finmap.singleton p v, ∅⟩
/-- The region entry R(p) = n alone. -/
def reg (p : Int) (n : Nat) : Assn := fun σ => σ = ⟨∅, Finmap.singleton p n⟩
def ex {α : Type} (P : α → Assn) : Assn := fun σ => ∃ x, P x σ
end Assn

infixr:35 " ∗ " => Assn.sep

/-- `{P} e {v. Q}` (OBJECT-L2 §5): from any σ ⊨ P with any disjoint frame σ_f (the whole store well-formed), no reachable
  configuration FAULTS, and every reached `ret a` evaluates to a value v and leaves σ′ ⊎ σ_f with σ′ ⊨ Q v, the whole store
  still well-formed (so a sequenced continuation needs no separate preservation theorem). -/
def Triple (P : Assn) (e : Tm₂) (Q : Atom₂ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    (∀ c, Steps₂ (e, σ ⊎ σf) c → ¬ Faults c) ∧
    (∀ a σ', Steps₂ (e, σ ⊎ σf) (.ret a, σ') →
      ∃ v σq, a.eval = some v ∧ Store.Disj σq σf ∧ σ' = σq ⊎ σf ∧ Store.WF σ' ∧ Q v σq)

/-- THE FRAME RULE, for EVERY L2 program e (OBJECT-L2 §5): no side condition, and no ⊢₂ judgement in its statement or proof. -/
theorem frame {P : Assn} {e : Tm₂} {Q : Atom₂ → Assn} (R : Assn) (h : Triple P e Q) :
    Triple (P ∗ R) e (fun v => Q v ∗ R) := by
  intro σ σf hPR hd hwf
  obtain ⟨σp, σr, hpr, rfl, hP, hR⟩ := hPR
  have hd' : Store.Disj σp (σr ⊎ σf) := by
    rw [Store.disj_union_left] at hd
    exact (Store.disj_union_right _ _ _).2 ⟨hpr, hd.1⟩
  have hdr : Store.Disj σr σf := ((Store.disj_union_left _ _ _).1 hd).2
  rw [Store.union_assoc] at hwf ⊢
  obtain ⟨hsafe, hpost⟩ := h σp (σr ⊎ σf) hP hd' hwf
  refine ⟨hsafe, fun a σ' hs => ?_⟩
  obtain ⟨v, σq, hv, hq, rfl, hw, hQ⟩ := hpost a σ' hs
  obtain ⟨hqr, hqf⟩ := (Store.disj_union_right _ _ _).1 hq
  exact ⟨v, σq ⊎ σr, hv, (Store.disj_union_left _ _ _).2 ⟨hqf, hdr⟩, (Store.union_assoc _ _ _).symm, hw,
    σq, σr, hqr, rfl, hQ, hR⟩

/-- Consequence. -/
theorem conseq {P P' : Assn} {e : Tm₂} {Q Q' : Atom₂ → Assn} (hP : ∀ σ, P' σ → P σ) (hQ : ∀ v σ, Q v σ → Q' v σ)
    (h : Triple P e Q) : Triple P' e Q' := by
  intro σ σf hp hd hwf
  obtain ⟨hs, hpost⟩ := h σ σf (hP σ hp) hd hwf
  refine ⟨hs, fun a σ' hst => ?_⟩
  obtain ⟨v, σq, hv, hq, he, hw, hQq⟩ := hpost a σ' hst
  exact ⟨v, σq, hv, hq, he, hw, hQ v σq hQq⟩

end VIRL2
