/-
  O95 layer L3, Lean arm. R1: `(w:cap) ; {w} ⊢₂ F : cap`, and the same for U (and U_tx, which R3 uses).
  Each derivation is built by `l3ty`, which applies ⊢₂'s rules syntax-directed; nothing here is a new rule (Z1).
-/
import VIRL3.Router

namespace VIRL3
open VIRL1 VIRL2

theorem mask_empty_nil' : Mask.empty ([] : List Bool) := by intro n; simp
theorem mask_empty_cons' {Δ : List Bool} (h : Mask.empty Δ) : Mask.empty (false :: Δ) := by
  intro n; cases n with
  | zero => simp
  | succ n => simpa using h n

/-- `Mask.only` on a concrete mask, by one decidable check over its indices. -/
theorem mask_only_of {Δ : List Bool} {n : Nat} (h0 : Δ[n]? = some true)
    (h : (List.range Δ.length).all (fun m => m == n || Δ[m]? != some true) = true) : Mask.only Δ n := by
  refine ⟨h0, fun m hm hm' => ?_⟩
  have hl : m < Δ.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm'; cases hm'
  have := List.all_eq_true.1 h m (List.mem_range.2 hl)
  simp [hm, hm'] at this

/-- Every capability of Δ goes to the right: the split a pure `let`'s bound term takes. -/
theorem split_left_empty : ∀ Δ : List Bool, Split Δ (Δ.map fun _ => false) Δ
  | [] => .nil
  | true :: Δ => .right (split_left_empty Δ)
  | false :: Δ => .none (split_left_empty Δ)

macro "l3ty" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none | apply Split.right
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl
  | exact HasTypeA₂.int | exact HasTypeA₂.bool
  | exact HasTypeA₂.var rfl rfl
  | refine HasTypeA₂.prim ?_
  | exact HasTypeL₂.nil | refine HasTypeL₂.cons ?_ ?_
  | exact HasType₂.retCap rfl (mask_only_of rfl (by decide))
  | refine HasType₂.ret ?_ ?_
  | refine HasType₂.letE (split_left_empty _) (Or.inr rfl) ?_ ?_
  | refine HasType₂.load rfl rfl ?_ ?_
  | refine HasType₂.store rfl rfl ?_ ?_ ?_
  | refine HasType₂.ite ?_ ?_ ?_))

/-- R1 for F. -/
theorem F_typed : HasType₂ [tcap] [true] F tcap := by
  simp only [F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf, List.findIdx,
    List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
  l3ty

/-- R1 for U. -/
theorem U_typed : HasType₂ [tcap] [true] U tcap := by
  simp only [U, Un, Ugen, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
  l3ty

/-- U_tx is typed too (R3 compares it with F). -/
theorem U_tx_typed : HasType₂ [tcap] [true] U_tx tcap := by
  simp only [U_tx, Utxn, Ugen, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add]
  l3ty

end VIRL3
