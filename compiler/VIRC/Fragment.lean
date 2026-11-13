/-
  O95 compiler (OBJECT-COMPILER, amend-23 §K), stage S1. C2 (a): the FIRST-ORDER fragment of L2, as a CHECKED predicate.
  A program is accepted iff it is closed (`wfB 0`) and every `lam`/`fix` atom in it is closed apart from its own binders
  (`fnOk`). A program outside the fragment is REJECTED by evaluating `Fragment.ok`; it is never miscompiled.
  Why closedness is the whole of C2 at S1: a closed function atom is left unchanged by every substitution ⟶₂ performs
  (`Tm.subst_wfB`), so its code needs no environment and a function value lowers to a code value (a label at S3).
-/
import VIRL2

namespace VIRC
open VIRL1 VIRL2

mutual
/-- Every variable is below `n` (a Bool twin of L1's `Atom.wf`, so the fragment test runs by evaluation). -/
def Atom.wfB : Nat → Atom₂ → Bool
  | n, .var m => decide (m < n)
  | _, .const _ => true
  | n, .prim _ as => Atom.wfLB n as
  | n, .lam _ e => Tm.wfB (n + 1) e
  | n, .fix _ _ e => Tm.wfB (n + 2) e
  | n, .pair a₁ a₂ => Atom.wfB n a₁ && Atom.wfB n a₂
  | n, .fst a => Atom.wfB n a
  | n, .snd a => Atom.wfB n a
  | n, .inl _ a => Atom.wfB n a
  | n, .inr _ a => Atom.wfB n a
def Atom.wfLB : Nat → List Atom₂ → Bool
  | _, [] => true
  | n, a :: as => Atom.wfB n a && Atom.wfLB n as
def Tm.wfB : Nat → Tm₂ → Bool
  | n, .ret a => Atom.wfB n a
  | n, .letE _ e₁ e₂ => Tm.wfB n e₁ && Tm.wfB (n + 1) e₂
  | n, .letOp _ as _ e => Atom.wfLB n as && Tm.wfB (n + 1) e
  | n, .app a₁ a₂ => Atom.wfB n a₁ && Atom.wfB n a₂
  | n, .ite a e₁ e₂ => Atom.wfB n a && Tm.wfB n e₁ && Tm.wfB n e₂
  | n, .case a e₁ e₂ => Atom.wfB n a && Tm.wfB (n + 1) e₁ && Tm.wfB (n + 1) e₂
end

mutual
/-- C2 (a): every function atom is closed apart from its own binders (λ: one, fix: two). -/
def Atom.fnOk : Atom₂ → Bool
  | .var _ => true
  | .const _ => true
  | .prim _ as => Atom.fnOkL as
  | .lam _ e => Tm.wfB 1 e && Tm.fnOk e
  | .fix _ _ e => Tm.wfB 2 e && Tm.fnOk e
  | .pair a₁ a₂ => Atom.fnOk a₁ && Atom.fnOk a₂
  | .fst a => Atom.fnOk a
  | .snd a => Atom.fnOk a
  | .inl _ a => Atom.fnOk a
  | .inr _ a => Atom.fnOk a
def Atom.fnOkL : List Atom₂ → Bool
  | [] => true
  | a :: as => Atom.fnOk a && Atom.fnOkL as
def Tm.fnOk : Tm₂ → Bool
  | .ret a => Atom.fnOk a
  | .letE _ e₁ e₂ => Tm.fnOk e₁ && Tm.fnOk e₂
  | .letOp _ as _ e => Atom.fnOkL as && Tm.fnOk e
  | .app a₁ a₂ => Atom.fnOk a₁ && Atom.fnOk a₂
  | .ite a e₁ e₂ => Atom.fnOk a && Tm.fnOk e₁ && Tm.fnOk e₂
  | .case a e₁ e₂ => Atom.fnOk a && Tm.fnOk e₁ && Tm.fnOk e₂
end

/-- C2's checked predicate: the compiler ACCEPTS exactly the programs on which this evaluates to `true`. -/
def Fragment.ok (e : Tm₂) : Bool := Tm.wfB 0 e && Tm.fnOk e

/-! ## Substitution leaves a term alone at or above its bound (the reason C2 makes function values environment-free). -/
mutual
theorem Atom.subst_wfB : ∀ (a : Atom₂) {n k : Nat} (v : Atom₂), Atom.wfB n a = true → n ≤ k → a.subst k v = a
  | .var m, n, k, v, h, hk => by
      simp only [Atom.wfB, decide_eq_true_eq] at h
      simp only [Atom.subst]; rw [if_pos (by omega)]
  | .const _, _, _, _, _, _ => rfl
  | .prim _ as, _, _, v, h, hk => by
      simp only [Atom.wfB] at h; simp only [Atom.subst, Atom.substL_wfB as v h hk]
  | .lam _ e, n, k, v, h, hk => by
      simp only [Atom.wfB] at h; simp only [Atom.subst, Tm.subst_wfB e (n := n + 1) (k := k + 1) v h (by omega)]
  | .fix _ _ e, n, k, v, h, hk => by
      simp only [Atom.wfB] at h; simp only [Atom.subst, Tm.subst_wfB e (n := n + 2) (k := k + 2) v h (by omega)]
  | .pair a₁ a₂, _, _, v, h, hk => by
      simp only [Atom.wfB, Bool.and_eq_true] at h
      simp only [Atom.subst, Atom.subst_wfB a₁ v h.1 hk, Atom.subst_wfB a₂ v h.2 hk]
  | .fst a, _, _, v, h, hk => by simp only [Atom.wfB] at h; simp only [Atom.subst, Atom.subst_wfB a v h hk]
  | .snd a, _, _, v, h, hk => by simp only [Atom.wfB] at h; simp only [Atom.subst, Atom.subst_wfB a v h hk]
  | .inl _ a, _, _, v, h, hk => by simp only [Atom.wfB] at h; simp only [Atom.subst, Atom.subst_wfB a v h hk]
  | .inr _ a, _, _, v, h, hk => by simp only [Atom.wfB] at h; simp only [Atom.subst, Atom.subst_wfB a v h hk]
theorem Atom.substL_wfB : ∀ (as : List Atom₂) {n k : Nat} (v : Atom₂), Atom.wfLB n as = true → n ≤ k →
    Atom.substL k v as = as
  | [], _, _, _, _, _ => rfl
  | a :: as, _, _, v, h, hk => by
      simp only [Atom.wfLB, Bool.and_eq_true] at h
      simp only [Atom.substL, Atom.subst_wfB a v h.1 hk, Atom.substL_wfB as v h.2 hk]
theorem Tm.subst_wfB : ∀ (e : Tm₂) {n k : Nat} (v : Atom₂), Tm.wfB n e = true → n ≤ k → e.subst k v = e
  | .ret a, _, _, v, h, hk => by simp only [Tm.wfB] at h; simp only [Tm.subst, Atom.subst_wfB a v h hk]
  | .letE _ e₁ e₂, n, k, v, h, hk => by
      simp only [Tm.wfB, Bool.and_eq_true] at h
      simp only [Tm.subst, Tm.subst_wfB e₁ v h.1 hk, Tm.subst_wfB e₂ (n := n + 1) (k := k + 1) v h.2 (by omega)]
  | .letOp _ as _ e, n, k, v, h, hk => by
      simp only [Tm.wfB, Bool.and_eq_true] at h
      simp only [Tm.subst, Atom.substL_wfB as v h.1 hk, Tm.subst_wfB e (n := n + 1) (k := k + 1) v h.2 (by omega)]
  | .app a₁ a₂, _, _, v, h, hk => by
      simp only [Tm.wfB, Bool.and_eq_true] at h
      simp only [Tm.subst, Atom.subst_wfB a₁ v h.1 hk, Atom.subst_wfB a₂ v h.2 hk]
  | .ite a e₁ e₂, _, _, v, h, hk => by
      simp only [Tm.wfB, Bool.and_eq_true] at h
      simp only [Tm.subst, Atom.subst_wfB a v h.1.1 hk, Tm.subst_wfB e₁ v h.1.2 hk, Tm.subst_wfB e₂ v h.2 hk]
  | .case a e₁ e₂, n, k, v, h, hk => by
      simp only [Tm.wfB, Bool.and_eq_true] at h
      simp only [Tm.subst, Atom.subst_wfB a v h.1.1 hk, Tm.subst_wfB e₁ (n := n + 1) (k := k + 1) v h.1.2 (by omega),
        Tm.subst_wfB e₂ (n := n + 1) (k := k + 1) v h.2 (by omega)]
end

end VIRC
