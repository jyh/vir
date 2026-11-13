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

/-- A mode term is typed under the dispatch's binder: md : int, w : cap, the capability available, result the world. -/
def ModeTyped (t : NT) : Prop := HasType₂ [tint, tcap] [false, true] (t.c ["md", "w"]) tcap

/-- Compile the named layer and type it. -/
macro "mty" : tactic => `(tactic| (
  simp only [ModeTyped, tableN, hdrN, readN, hdrbN, hdrdN, shdrN, fixlensN, dhdrN, slenN, snlenN, scopyN, buildN, lensN, symN,
    decodeN, symdN, lenxN, dstdN, dstxN, copyN, dh2N, dh3N, dh4N, clreadN, clputN, lsymN, lrepN, repN, reqN, reqDecN, reqKN,
    rejN, bZeroN, bCountN, bNextN, bRestN, bLeftN, bSymsN,
    NT.c, NA.c, List.map, List.idxOf, List.findIdx, List.findIdx.go, String.reduceBEq, cond_true, cond_false]
  dty))

theorem table_typed : ModeTyped tableN := by mty
theorem hdr_typed : ModeTyped hdrN := by mty
theorem read_typed : ModeTyped readN := by mty
theorem hdrb_typed : ModeTyped hdrbN := by mty
theorem hdrd_typed : ModeTyped hdrdN := by mty
theorem shdr_typed : ModeTyped shdrN := by mty
theorem fixlens_typed : ModeTyped fixlensN := by mty
theorem dhdr_typed : ModeTyped dhdrN := by mty
theorem slen_typed : ModeTyped slenN := by mty
theorem snlen_typed : ModeTyped snlenN := by mty
theorem scopy_typed : ModeTyped scopyN := by mty
theorem build_typed : ModeTyped buildN := by mty
theorem lens_typed : ModeTyped lensN := by mty
theorem sym_typed : ModeTyped symN := by mty
theorem decode_typed : ModeTyped decodeN := by mty
theorem symd_typed : ModeTyped symdN := by mty
theorem lenx_typed : ModeTyped lenxN := by mty
theorem dstd_typed : ModeTyped dstdN := by mty
theorem dstx_typed : ModeTyped dstxN := by mty
theorem copy_typed : ModeTyped copyN := by mty
theorem dh2_typed : ModeTyped dh2N := by mty
theorem dh3_typed : ModeTyped dh3N := by mty
theorem dh4_typed : ModeTyped dh4N := by mty
theorem clread_typed : ModeTyped clreadN := by mty
theorem clput_typed : ModeTyped clputN := by mty
theorem lsym_typed : ModeTyped lsymN := by mty
theorem lrep_typed : ModeTyped lrepN := by mty
theorem rep_typed : ModeTyped repN := by mty

theorem modes_typed : ∀ kt ∈ modes, ModeTyped kt.2 := by
  intro kt hkt
  simp only [modes, List.mem_cons, List.mem_nil_iff, or_false] at hkt
  rcases hkt with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h
  exacts [table_typed, hdr_typed, read_typed, hdrb_typed, hdrd_typed, shdr_typed, fixlens_typed, dhdr_typed, slen_typed,
    snlen_typed, scopy_typed, build_typed, lens_typed, sym_typed, decode_typed, symd_typed, lenx_typed, dstd_typed, dstx_typed,
    copy_typed, dh2_typed, dh3_typed, dh4_typed, clread_typed, clput_typed, lsym_typed, lrep_typed, rep_typed]

/-- The dispatch is typed when every branch is: each test is `md = k` on the int at #0, the fall-through returns the world. -/
theorem disp_typed : ∀ ms : List (Int × NT), (∀ kt ∈ ms, ModeTyped kt.2) → ModeTyped (dispN ms)
  | [], _ => by simp only [ModeTyped, dispN]; mty
  | (k, t) :: r, h => by
    have ht : ModeTyped t := h (k, t) (by simp)
    have hr : ModeTyped (dispN r) := disp_typed r (fun kt hkt => h kt (by simp [hkt]))
    simp only [ModeTyped] at ht hr ⊢
    simp only [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, String.reduceBEq, cond_true, cond_false]
    refine HasType₂.ite ?_ ht hr
    dty

/-- **The step is a well-typed L2 term, linear in the world:** `[w : cap] ; [w available] ⊢₂ stepT : cap`. -/
theorem stepT_typed : HasType₂ [tcap] [true] stepT tcap := by
  simp only [stepT, stepN, NT.c, NA.c, List.map, List.idxOf, List.findIdx, List.findIdx.go, String.reduceBEq, cond_true,
    cond_false]
  refine HasType₂.load rfl rfl HasTypeA₂.int ?_
  exact disp_typed modes modes_typed

end VIRDeflate.Step
