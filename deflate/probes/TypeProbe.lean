import VIRDeflate.Dispatch
namespace VIRDeflate.Step
open VIRL1 VIRL2

theorem mask_empty_nil' : Mask.empty ([] : List Bool) := by intro n; simp
theorem mask_empty_cons' {Δ : List Bool} (h : Mask.empty Δ) : Mask.empty (false :: Δ) := by
  intro n; cases n with
  | zero => simp
  | succ n => simpa using h n
theorem mask_only_of {Δ : List Bool} {n : Nat} (h0 : Δ[n]? = some true)
    (h : (List.range Δ.length).all (fun m => m == n || Δ[m]? != some true) = true) : Mask.only Δ n := by
  refine ⟨h0, fun m hm hm' => ?_⟩
  have hl : m < Δ.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm'; cases hm'
  have := List.all_eq_true.1 h m (List.mem_range.2 hl)
  simp [hm, hm'] at this
theorem split_left_empty : ∀ Δ : List Bool, Split Δ (Δ.map fun _ => false) Δ
  | [] => .nil
  | true :: Δ => .right (split_left_empty Δ)
  | false :: Δ => .none (split_left_empty Δ)

macro "dty" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none | apply Split.right
  | exact mask_empty_nil' | apply mask_empty_cons'
  | exact Or.inr rfl
  | exact HasTypeA₂.int | exact HasTypeA₂.bool
  | exact HasTypeA₂.var rfl rfl
  | refine HasTypeA₂.prim ?_
  | refine HasTypeA₂.pair ?_ ?_ | refine HasTypeA₂.fst ?_ | refine HasTypeA₂.snd ?_
  | exact HasTypeL₂.nil | refine HasTypeL₂.cons ?_ ?_
  | exact HasType₂.retCap rfl (mask_only_of rfl (by decide))
  | refine HasType₂.ret ?_ ?_
  | refine HasType₂.letE (split_left_empty _) (Or.inr rfl) ?_ ?_
  | refine HasType₂.load rfl rfl ?_ ?_
  | refine HasType₂.store rfl rfl ?_ ?_ ?_
  | refine HasType₂.ite ?_ ?_ ?_))

theorem hdr_typed : HasType₂ [tcap] [true] hdrT tcap := by
  simp only [hdrT, hdrN, reqN, NT.c, NA.c, List.map, List.idxOf, List.findIdx, List.findIdx.go, cK, cACC, cWT, cRET, cMODE,
    mREAD, mHDRB]
  dty

theorem read_typed : HasType₂ [tcap] [true] readT tcap := by
  simp only [readT, readN, NT.c, NA.c, List.map, List.idxOf, List.findIdx, List.findIdx.go]
  dty
end VIRDeflate.Step
