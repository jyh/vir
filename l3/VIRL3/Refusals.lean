/-
  O95 layer L3, Lean arm. The two refusals (OBJECT-L3 §3.6; Z8 predicts each ≤ 15 lines of proof).
  R7: F with `EXIT(1)` replaced by `ret 1` is ILL-TYPED (the world is leaked: M4 at program scale).
  R8: F on a frame with the magic correct and sender = NS is TYPED (R1) and INDEX-FAULTS at the bucket load; no triple holds
  from that store (M3 at program scale). G3 (a): bounds are the logic's, not the term's.
-/
import VIRL3.Inequality

namespace VIRL3
open VIRL1 VIRL2

/-- R7's variant: F's too-short exit returns the integer 1 instead of the world. -/
def F7n : NT :=
  match Fn with
  | .op x τ o as (.ite a e₁ _) => .op x τ o as (.ite a e₁ (.ret (.i 1)))
  | e => e

def F7 : Tm₂ := F7n.c ["w"]

/-- R7: no type at all for F7. -/
theorem R7 : ∀ τ, ¬ HasType₂ [tcap] [true] F7 τ := by
  intro τ h
  simp only [F7, F7n, Fn, NT.c, NA.c, le, List.map, List.idxOf, List.findIdx, List.findIdx.go, String.reduceBEq,
    cond_true, cond_false, Nat.reduceAdd, Nat.zero_add] at h
  cases h with
  | load _ _ _ h =>
    cases h with
    | ite _ _ h => cases h with
      | ret hΔ _ => exact hΔ 1 rfl

/-- R8's store: LEN 24, the magic, sender byte 0 = 4 = NS (so sender = NS), topic 0. -/
def σ8 : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (7, 4)]

/-! ## σ8 is well-formed (so R8 is not vacuous): the alloc small axiom, then each write keeps WF. -/
theorem wf_store_getD {σ : Store} (h : σ.WF) (p i v : Int) : ((Store.store p i v σ).getD σ).WF := by
  unfold Store.store
  split
  · next n hn =>
    split
    · next hr => exact wf_insert_mem ((h.domH _).2 ⟨p, n, hn, by unfold Store.InRegion; omega⟩) h
    · exact h
  · exact h

theorem wf_foldl : ∀ (cells : List (Int × Int)) (σ : Store), σ.WF →
    (cells.foldl (fun σ c => (Store.store 0 c.1 c.2 σ).getD σ) σ).WF
  | [], _, h => h
  | c :: cs, σ, h => wf_foldl cs _ (wf_store_getD h 0 c.1 c.2)

theorem wf_mkWorld (cells : List (Int × Int)) : (mkWorld cells).WF := by
  refine wf_foldl cells _ ?_
  obtain ⟨v, σq, hop, -, hwf, -⟩ := alloc_axiom 87 (by decide) Store.empty Store.empty rfl (disj_empty_left _)
    (by rw [Store.empty_union]; exact wf_empty)
  rw [Store.empty_union, Store.union_empty] at hop
  rw [Store.union_empty] at hwf
  have he : opStep .alloc [.const (.int 87)] Store.empty =
      some (.const (.cap 0), ((Store.alloc 87 Store.empty).map Prod.snd).getD Store.empty) := rfl
  rw [he] at hop; cases hop; exact hwf

set_option maxRecDepth 100000 in
/-- The run stops at the bucket load, cell K + 4 = 87, one past the 87-cell world. -/
theorem F8_stuck : ∃ rest, (run₂ 80 (closeW F, σ8)).1 =
    .letOp .load [.const (.cap 0), .prim .add [.const (.int 83), .const (.int 4)]] tint rest := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- R8: from σ8 the run reaches a configuration that FAULTS, so no triple whose precondition admits σ8 holds. -/
theorem R8 {P : Assn} {Q : Atom₂ → Assn} (hP : P σ8) : ¬ Triple P (closeW F) Q := by
  intro h
  have hwf := wf_mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (7, 4)]
  have hs := (h σ8 Store.empty hP ⟨Finmap.disjoint_empty _ |>.symm, Finmap.disjoint_empty _ |>.symm⟩
    (by rw [Store.union_empty]; exact hwf)).1
  rw [Store.union_empty] at hs
  obtain ⟨rest, hr⟩ := F8_stuck
  apply hs _ (run₂_steps 80 _)
  refine ⟨by rw [hr]; exact id, fun c' hc => ?_⟩
  have he : run₂ 80 (closeW F, σ8) = ((run₂ 80 (closeW F, σ8)).1, (run₂ 80 (closeW F, σ8)).2) := rfl
  rw [he, hr] at hc
  obtain ⟨vs, v, σ', h₁, h₂, -⟩ := step₂_letOp_inv hc
  cases h₁
  change opStep .load [.const (.cap 0), .const (Const.ofL1 (L1.Const.int (83 + 4)))] _ = _ at h₂
  have hnone : opStep .load [.const (.cap 0), .const (Const.ofL1 (L1.Const.int (83 + 4)))]
      (run₂ 80 (closeW F, σ8)).2 = none := rfl
  rw [hnone] at h₂; cases h₂

end VIRL3
