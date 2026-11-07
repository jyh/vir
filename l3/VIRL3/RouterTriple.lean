/-
  O95 layer L3, Lean arm. R4, the router triple of OBJECT-L3 §3.3 for F, proved by SEQUENCING OBJECT-L2 §5's rules (Z5):
  `letOp_rule` with the load/store small axioms at the world (`load_at`, `store_at`), `pure_step_rule` for each pure `let` and
  `if`, `ret_rule'` at the exits. ⟶₂ is not unfolded; the two determinism facts a pure step needs come from L1's `determinism`.
  The layout's pure part is carried as Lean hypotheses ({P ∗ ⌜φ⌝} e {Q} is φ → {P} e {Q}); `RegionAt` indexes cells by ABSOLUTE
  address, so the frame's fields are read at p + i.
-/
import VIRL3.Rollback

namespace VIRL3
open VIRL1 VIRL2

theorem det_ite {a : Atom₂} {e₁ e₂ e' : Tm₂} (hs : Step (.ite a e₁ e₂) e') :
    ∀ σ c, Step₂ (.ite a e₁ e₂, σ) c → c = (e', σ) := by
  intro σ c h; cases h with | pure h' => rw [← determinism hs h']

theorem det_letRet {τ : Ty₂} {a : Atom₂} {e₂ e' : Tm₂} (hs : Step (.letE τ (.ret a) e₂) e') :
    ∀ σ c, Step₂ (.letE τ (.ret a) e₂, σ) c → c = (e', σ) := by
  intro σ c h; cases h with
  | pure h' => rw [← determinism hs h']
  | letStep h' => exact (step₂_ret_none h').elim

/-- The frame's fields, read at absolute addresses in the world at p. -/
def MgA (f : Int → Int) (p : Int) : Int := f (p + 3) + (256 * f (p + 4) + (65536 * f (p + 5) + 16777216 * f (p + 6)))
def SvA (f : Int → Int) (p : Int) : Int := f (p + 7) + (256 * f (p + 8) + (65536 * f (p + 9) + 16777216 * f (p + 10)))
def TvA (f : Int → Int) (p : Int) : Int := f (p + 11) + (256 * f (p + 12) + (65536 * f (p + 13) + 16777216 * f (p + 14)))
/-- The ACL cell and the bucket cell of the frame's sender and topic. -/
def aclA (f : Int → Int) (p : Int) : Int := p + (67 + (SvA f p * 4 + TvA f p))
def bktA (f : Int → Int) (p : Int) : Int := p + (83 + SvA f p)

/-- F emits: a long frame, the magic, the ACL bit, a token. -/
def Emits (f : Int → Int) (p : Int) : Prop :=
  24 ≤ f (p + 0) ∧ MgA f p = MAGIC ∧ f (aclA f p) = 1 ∧ 0 < f (bktA f p)

open Classical in
/-- R4's post-state: the bucket decremented iff F emits, and the out cells (CODE at p + 1, PAY at p + 2). -/
noncomputable def postF (f : Int → Int) (p : Int) : Int → Int :=
  if 24 ≤ f (p + 0) then
    if Emits f p then
      Function.update (Function.update (Function.update f (bktA f p) (f (bktA f p) - 1)) (p + 1) 0) (p + 2) 24
    else Function.update f (p + 1) 2
  else Function.update f (p + 1) 1

theorem ite_true_rule {P : Assn} {a : Atom₂} {e₁ e₂ : Tm₂} {Q : Atom₂ → Assn} {c : Const}
    (ha : Atom.eval a = some (.const c)) (hb : S₂.toBool c = some true) (h : Triple P e₁ Q) : Triple P (.ite a e₁ e₂) Q :=
  pure_step_rule (.iteT ha hb) (det_ite (.iteT ha hb)) h

theorem ite_false_rule {P : Assn} {a : Atom₂} {e₁ e₂ : Tm₂} {Q : Atom₂ → Assn} {c : Const}
    (ha : Atom.eval a = some (.const c)) (hb : S₂.toBool c = some false) (h : Triple P e₂ Q) : Triple P (.ite a e₁ e₂) Q :=
  pure_step_rule (.iteF ha hb) (det_ite (.iteF ha hb)) h

theorem letRet_rule {P : Assn} {τ : Ty₂} {a v : Atom₂} {e₂ : Tm₂} {Q : Atom₂ → Assn}
    (ha : Atom.eval a = some v) (h : Triple P (e₂.subst 0 v) Q) : Triple P (.letE τ (.ret a) e₂) Q :=
  pure_step_rule (.letRet ha) (det_letRet (.letRet ha)) h

/-- One load from the world at p (relative index i), its value substituted. -/
macro "ld" : tactic => `(tactic| (refine letOp_rule rfl (load_at _ 87 _ _ ?_) (fun v => pre_pure (fun hv => ?_)); (first | omega | (simp only [A, K, NW, NS, NTp, SvA, TvA, MgA] at *; omega)); subst hv; simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]))
/-- One store into the world at p, its result (the world) substituted. -/
macro "st" : tactic => `(tactic| (refine letOp_rule rfl (store_at _ 87 _ _ _ ?_) (fun c => pre_pure (fun hc => ?_)); (first | omega | (simp only [A, K, NW, NS, NTp, SvA, TvA, MgA] at *; omega)); subst hc; simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]))
/-- A pure `let x = ret a`, its value given. -/
macro "pl" v:term : tactic => `(tactic| (refine letRet_rule (v := Atom.const (Const.int ($v))) (by simp [Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, MgA, SvA, TvA]) ?_; try simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]))

set_option linter.unusedSimpArgs false in
/-- R4 (OBJECT-L3 §3.3) for F: from the world alone, F returns the world, its contents `postF f p`. -/
theorem R4 {p : Int} {f : Int → Int} (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p) (ht4 : TvA f p < 4) :
    Triple (RegionAt p 87 f) (closeAt p F) (fun v σ => v = .const (.cap p) ∧ RegionAt p 87 (postF f p) σ) := by
  simp only [SvA, TvA] at hs0 hs4 ht0 ht4
  simp only [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  ld
  by_cases hn : 24 ≤ f (p + 0)
  · have hn' : 24 ≤ f p := by simpa using hn
    refine ite_true_rule rfl (by simp [Const.toBool, Const.ofL1, hn']) ?_
    ld; ld; ld; ld; pl (MgA f p)
    ld; ld; ld; ld; pl (SvA f p)
    ld; ld; ld; ld; pl (TvA f p)
    ld; ld
    by_cases he : Emits f p
    · refine ite_true_rule rfl (by simp [Const.toBool, Const.ofL1, Emits, aclA, bktA, A, K, NW, NS, NTp, MAGIC] at he ⊢; simp [he]) ?_
      st; st; st
      refine ret_rule' rfl (fun σ h => ⟨rfl, ?_⟩)
      simpa [postF, hn', he, bktA, K, A, NW, NS, NTp] using h
    · refine ite_false_rule rfl (by simp [Const.toBool, Const.ofL1, Emits, aclA, bktA, A, K, NW, NS, NTp, MAGIC] at he ⊢; omega) ?_
      st
      refine ret_rule' rfl (fun σ h => ⟨rfl, ?_⟩)
      simpa [postF, hn', he] using h
  · have hn' : ¬ 24 ≤ f p := by simpa using hn
    refine ite_false_rule rfl (by simp [Const.toBool, Const.ofL1, hn']) ?_
    refine letOp_rule rfl (store_at _ 87 _ 1 1 (by decide)) (fun c => pre_pure (fun hc => ?_))
    subst hc; simp only [Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Int.reduceAdd]
    exact ret_rule' rfl (fun σ h => ⟨rfl, by simpa [postF, hn'] using h⟩)

/-- R5 (OBJECT-L3 §3.4), the contents half: F's post-state agrees with f off the bucket cell and the out cells. -/
theorem R5_contents (f : Int → Int) (p a : Int) (hb : a ≠ bktA f p) (h1 : a ≠ p + 1) (h2 : a ≠ p + 2) :
    postF f p a = f a := by
  unfold postF; split_ifs <;> simp [Function.update_apply, hb, h1, h2]

/-- R5, the caller half: the router triple holds beside ANY frame R the caller owns, with no premise naming R — ONE
  application of L2's frame rule (Z6). -/
theorem R5_frame {p : Int} {f : Int → Int} (R : Assn) (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p)
    (ht4 : TvA f p < 4) :
    Triple (RegionAt p 87 f ∗ R) (closeAt p F)
      (fun v => (fun σ => v = .const (.cap p) ∧ RegionAt p 87 (postF f p) σ) ∗ R) :=
  frame R (R4 hs0 hs4 ht0 ht4)

end VIRL3
