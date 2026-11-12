/-
OBJECT-DEFLATE under X1 (a): the step under ⊢₂ (DECLARATIONS-DEFLATE.md, the file list: "`Typing.lean`: the step under ⊢₂";
STATUS-vir 293 (a); priced by df-probe-004). The step is a well-typed L2 term, linear in its one capability:
`HasType₂ [tcap] [true] stepT tcap`.
Built compositionally: each of the 28 mode terms is typed under the dispatch's binder (`[md : int, w : cap]`, the capability
available), the dispatch by induction over the mode list, and the step by L2's `load` rule on the mode cell. The tactic is
l3's `l3ty` (copied; l3 is not a dependency, S-4) with pairs, projections and `app` added, and l3's simp set for the variable
indices (`String.reduceBEq`, `cond_true`, `cond_false`). `BITc` is closed and typed at [] (Step.lean); at TABLE's one call
site it is typed in that site's own context by the same proof.
l1/ and l2/ are imported and never edited (D2).
-/
import VIRDeflate.Dispatch
-- MUTANT: TABLE's second store goes through the SPENT capability w (linearity). Must be RED inside table_typed.

namespace VIRDeflate.Step
open VIRL1 VIRL2

theorem mask_empty_nil : Mask.empty ([] : List Bool) := by intro n; simp
theorem mask_empty_cons {Δ : List Bool} (h : Mask.empty Δ) : Mask.empty (false :: Δ) := by
  intro n; cases n with
  | zero => simp
  | succ n => simpa using h n
theorem mask_empty_map (Δ : List Bool) : Mask.empty (Δ.map fun _ => false) := by
  intro n h
  rw [List.getElem?_map] at h
  cases h' : Δ[n]? <;> simp [h'] at h
theorem mask_only_of {Δ : List Bool} {n : Nat} (h0 : Δ[n]? = some true)
    (h : (List.range Δ.length).all (fun m => m == n || Δ[m]? != some true) = true) : Mask.only Δ n := by
  refine ⟨h0, fun m hm hm' => ?_⟩
  have hl : m < Δ.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm'; cases hm'
  have := List.all_eq_true.1 h m (List.mem_range.2 hl)
  simp [hm, hm'] at this
/-- A pure `let`: every capability goes to the body. -/
theorem split_left_empty : ∀ Δ : List Bool, Split Δ (Δ.map fun _ => false) Δ
  | [] => .nil
  | true :: Δ => .right (split_left_empty Δ)
  | false :: Δ => .none (split_left_empty Δ)

/-- `BITc` at TABLE's call site under the dispatch: ti, tb, md : int, w : cap. -/
theorem BITc_typed_table : HasTypeA₂ [tint, tint, tint, tcap] BITc (.arr (.prod tint tint) tint) := by
  simp only [BITc, STRIPc, STRIP, POW, Atom.subst, Tm.subst, Atom.substL, ple, plt, psub, pmul, padd]
  repeat' (first
    | exact Split.nil | apply Split.none
    | exact mask_empty_replicate _ | exact mask_empty_nil | apply mask_empty_cons
    | (right; rfl)
    | rfl
    | apply HasType₂.ret | apply HasType₂.letE | apply HasType₂.app | apply HasType₂.ite
    | apply HasTypeA₂.var | apply HasTypeA₂.int | apply HasTypeA₂.prim
    | apply HasTypeA₂.pair | apply HasTypeA₂.fst | apply HasTypeA₂.snd
    | apply fix_typed rfl rfl
    | apply HasTypeL₂.cons | apply HasTypeL₂.nil)

/-- l3's `l3ty`, with pairs, projections, `app` and the closed `BITc`. -/
macro "dty" : tactic => `(tactic| repeat' (first
  | exact Split.nil | apply Split.none | apply Split.right
  | exact mask_empty_map _
  | exact mask_empty_nil | apply mask_empty_cons
  | exact Or.inr rfl
  | exact BITc_typed_table
  | exact HasTypeA₂.int | exact HasTypeA₂.bool
  | exact HasTypeA₂.var rfl rfl
  | refine HasTypeA₂.prim ?_
  | refine HasTypeA₂.pair ?_ ?_
  | (apply HasTypeA₂.fst; exact HasTypeA₂.var rfl rfl) | (apply HasTypeA₂.snd; exact HasTypeA₂.var rfl rfl)
  | refine HasTypeA₂.fst ?_ | refine HasTypeA₂.snd ?_
  | exact HasTypeL₂.nil | refine HasTypeL₂.cons ?_ ?_
  | exact HasType₂.retCap rfl (mask_only_of rfl (by decide))
  | refine HasType₂.ret ?_ ?_
  | exact HasType₂.app (mask_empty_map _) BITc_typed_table (HasTypeA₂.pair (HasTypeA₂.var rfl rfl) (HasTypeA₂.var rfl rfl))
  | refine HasType₂.letE (split_left_empty _) (Or.inr rfl) ?_ ?_
  | refine HasType₂.load rfl rfl ?_ ?_
  | refine HasType₂.store rfl rfl ?_ ?_ ?_
  | refine HasType₂.ite ?_ ?_ ?_))

/-- copy of tableN -/
def tableM : NT :=
  .op "tb" tint .load [.v "w", .i cTB] <|
  .op "ti" tint .load [.v "w", .i cTI] <|
  .letE "x" tint (.app (.atom BITc) (.pair (.v "tb") (.v "ti"))) <|
  .op "w1" tcap .store [.v "w", .p2 .add (.i BT) (.p2 .add (.p2 .mul (.i 8) (.v "tb")) (.v "ti")), .v "x"] <|
  .letE "nb" (.prod tint tint)
    (.ite (.p2 .eq (.v "ti") (.i 7)) (.ret (.pair (.p2 .add (.v "tb") (.i 1)) (.i 0)))
      (.ret (.pair (.v "tb") (.p2 .add (.v "ti") (.i 1))))) <|
  .op "w2" tcap .store [.v "w", .i cTB, .fst (.v "nb")] <|
  .op "w3" tcap .store [.v "w2", .i cTI, .snd (.v "nb")] <|
  .ite (.p2 .eq (.fst (.v "nb")) (.i 256))
    (.op "w4" tcap .store [.v "w3", .i cMODE, .i mHDR] (.ret (.v "w4")))
    (.ret (.v "w3"))

def ModeTyped (t : NT) : Prop := HasType₂ [tint, tcap] [false, true] (t.c ["md", "w"]) tcap

theorem table_typed : ModeTyped tableM := by
  simp only [ModeTyped, tableM, NT.c, NA.c, List.map, List.idxOf, List.findIdx, List.findIdx.go, String.reduceBEq, cond_true,
    cond_false]
  dty
end VIRDeflate.Step
