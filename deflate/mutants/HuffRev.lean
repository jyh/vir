/-
OBJECT-DEFLATE, Appendix S §S4: canonical Huffman codes, the construction and `decode`. D5's CANONICAL-CODE group
(deflate/DECLARATIONS-DEFLATE.md): this file and Kraft.lean.

The representation is S4's assignment itself, kept in the form that assignment produces:
`first[ℓ]` is `next_code[ℓ]` before any symbol takes it, and `syms[ℓ]` lists the symbols of length ℓ in increasing index,
which is the order `next_code[lens[i]]++` hands them codes. So the symbol whose code is the ℓ-bit value `v` is
`syms[ℓ][v - first[ℓ]]` when `first[ℓ] ≤ v < first[ℓ] + bl_count[ℓ]`, and no symbol has it otherwise.
-/
import VIRDeflate.Bits

namespace VIRDeflate.MutRev

/-- A canonical code, as S4's assignment leaves it. Arrays are indexed by length ℓ ∈ 0..15 (entry 0 unused). -/
structure Code where
  count : Array Nat
  first : Array Nat
  syms : Array (Array Nat)

/-- S4: `bl_count[ℓ] := #{ i : lens[i] = ℓ }` for ℓ ≥ 1, and `bl_count[0] := 0`. -/
def blCount (lens : Array Nat) (l : Nat) : Nat :=
  if l = 0 then 0 else lens.foldl (fun c x => if x = l then c + 1 else c) 0

/-- S4: `code := 0 ; for ℓ in 1..15: code := (code + bl_count[ℓ-1]) << 1 ; next_code[ℓ] := code`. -/
def nextCodes (lens : Array Nat) : Array Nat :=
  ((List.range' 1 15).foldl
    (fun (acc : Nat × Array Nat) l =>
      let c := (acc.1 + blCount lens (l - 1)) <<< 1
      (c, acc.2.push c))
    (0, #[0])).2

/-- The symbols of length ℓ, in increasing index. -/
def symsOf (lens : Array Nat) (l : Nat) : Array Nat :=
  ((List.range lens.size).foldl (fun a i => if lens.getD i 0 = l then a.push i else a) #[]).reverse

/-- S4's construction with no completeness check: the assignment alone. -/
def assign (lens : Array Nat) : Code :=
  { count := (List.range 16).toArray.map (blCount lens)
    first := nextCodes lens
    syms := (List.range 16).toArray.map (symsOf lens) }

/-- S4: `left := 1 ; for ℓ in 1..15: left := 2·left − bl_count[ℓ]`, stopping at the first ℓ where `left < 0`
(`none` = REJECT "over-subscribed"); otherwise the final `left`. -/
def leftAfter (lens : Array Nat) : Option Int :=
  (List.range' 1 15).foldl
    (fun (acc : Option Int) l =>
      match acc with
      | none => none
      | some left =>
        let left' := 2 * left - (blCount lens l : Int)
        if left' < 0 then none else some left')
    (some 1)

/-- "the code has exactly one symbol, of length 1". -/
def oneSymbolLenOne (lens : Array Nat) : Bool :=
  blCount lens 1 = 1 && (List.range' 2 14).all (fun l => blCount lens l = 0)

/-- How the incomplete clause applies. S4 as written (`normal`); S6's code-length code, *"no exception"* (`strict`);
S4's note on the empty distance code (`dist`): an all-zero distance code is accepted. -/
inductive Mode where
  | normal
  | strict
  | dist
  deriving DecidableEq

/-- S4: `code(lens)`, with its two REJECTs. -/
def code (lens : Array Nat) (mode : Mode := .normal) : M Code :=
  match leftAfter lens with
  | none => reject "over-subscribed"
  | some left =>
    let empty := lens.all (· = 0)
    let exempt := match mode with
      | .normal => oneSymbolLenOne lens
      | .strict => false
      | .dist => oneSymbolLenOne lens || empty
    if left > 0 && !exempt then reject "incomplete" else pure (assign lens)

/-- `decode` as a loop over the code length ℓ: `v` is the ℓ-bit value read so far, MSB first. -/
def decodeGo (C : Code) : Nat → Nat → Nat → M Nat
  | 0, _, _ => reject "invalid code"
  | fuel + 1, l, v => do
    let x ← bit
    let v := 2 * v + x
    let f := C.first.getD l 0
    let n := C.count.getD l 0
    if f ≤ v ∧ v < f + n then
      return (C.syms.getD l #[]).getD (v - f) 0
    else
      decodeGo C fuel (l + 1) v

/-- S4: `decode(C)` — read bits MSB-first until they form a code of C; REJECT "invalid code" if none can (all codes have
length ≤ 15, so after 15 bits none can). -/
def decode (C : Code) : M Nat := decodeGo C 15 1 0

/-! ## `Code` is S4's assignment (STAGE-DEFLATE limit (b), STATUS-vir 289 (b))

S4 assigns symbol `i` (with `lens[i] = ℓ ≠ 0`) the ℓ-bit code `next_code[ℓ]++`, taken in increasing `i`; so symbol `i`'s code is
`next_code[ℓ]` plus the number of earlier symbols of length ℓ (`codeOf`). `lookup` is the test `decodeGo` makes at length ℓ.
`lookup_codeOf` and `lookup_some` say the two agree in both directions, for every length 1..15. -/

/-- S4's per-symbol assignment, literally. -/
def codeOf (lens : Array Nat) (i : Nat) : Nat :=
  (nextCodes lens).getD (lens.getD i 0) 0 +
    ((List.range i).filter (fun j => lens.getD j 0 = lens.getD i 0)).length

/-- The test `decodeGo` makes on the ℓ-bit value `v`. -/
def lookup (C : Code) (l v : Nat) : Option Nat :=
  if C.first.getD l 0 ≤ v ∧ v < C.first.getD l 0 + C.count.getD l 0 then
    some ((C.syms.getD l #[]).getD (v - C.first.getD l 0) 0)
  else none

theorem decodeGo_succ (C : Code) (fuel l v : Nat) :
    decodeGo C (fuel + 1) l v = (do
      let x ← bit
      match lookup C l (2 * v + x) with
      | some s => pure s
      | none => decodeGo C fuel (l + 1) (2 * v + x)) := by
  simp only [decodeGo, lookup]
  congr 1; funext x
  split_ifs <;> rfl

theorem foldl_push_filter (p : Nat → Prop) [DecidablePred p] (xs : List Nat) (acc : Array Nat) :
    xs.foldl (fun a i => if p i then a.push i else a) acc = acc ++ (xs.filter p).toArray := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x
    · simp only [List.foldl_cons, h, if_true, ih, List.filter_cons, decide_true]
      apply Array.ext' ; simp
    · simp only [List.foldl_cons, h, if_false, ih, List.filter_cons, decide_false]
      rfl

/-- The symbols of length ℓ, as a list. -/
def symsL (lens : Array Nat) (l : Nat) : List Nat :=
  (List.range lens.size).filter (fun i => lens.getD i 0 = l)

theorem symsOf_eq (lens : Array Nat) (l : Nat) : symsOf lens l = (symsL lens l).toArray := by
  unfold symsOf symsL
  rw [foldl_push_filter (fun i => lens.getD i 0 = l)]
  simp

theorem foldl_count (l : Nat) (xs : List Nat) (c : Nat) :
    xs.foldl (fun c x => if x = l then c + 1 else c) c = c + xs.count l := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = l
    · simp only [List.foldl_cons, h, if_true]; rw [ih]; simp [List.count_cons]; omega
    · simp only [List.foldl_cons, h, if_false]; rw [ih]; simp [List.count_cons, h]

theorem symsL_length (lens : Array Nat) (l : Nat) : (symsL lens l).length = lens.toList.count l := by
  unfold symsL
  have hm : lens.toList = (List.range lens.size).map (fun i => lens.getD i 0) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp at h1
      simp [Array.getD, h1]
  rw [← List.countP_eq_length_filter, List.count, hm, List.countP_map]
  congr 1

theorem blCount_eq (lens : Array Nat) (l : Nat) (hl : l ≠ 0) : blCount lens l = (symsL lens l).length := by
  unfold blCount
  rw [if_neg hl, symsL_length, ← Array.foldl_toList, foldl_count]
  simp

theorem assign_count (lens : Array Nat) (l : Nat) (hl : l < 16) :
    (assign lens).count.getD l 0 = blCount lens l := by
  simp [assign, Array.getD, hl]

theorem assign_syms (lens : Array Nat) (l : Nat) (hl : l < 16) :
    (assign lens).syms.getD l #[] = symsOf lens l := by
  simp [assign, Array.getD, hl]

theorem assign_first (lens : Array Nat) (l : Nat) : (assign lens).first.getD l 0 = (nextCodes lens).getD l 0 := rfl

/-- The filtered range, split at a member `i`: its index in the filtered list is the number of earlier members. -/
theorem filter_range_at (p : Nat → Prop) [DecidablePred p] (n i : Nat) (hi : i < n) (hp : p i) :
    ∃ h : ((List.range i).filter p).length < ((List.range n).filter p).length,
      ((List.range n).filter p)[((List.range i).filter p).length] = i := by
  have hsplit : List.range n = List.range i ++ i :: List.range' (i + 1) (n - i - 1) := by
    rw [show n = i + (1 + (n - i - 1)) by omega, List.range_add, List.range_add]
    simp [List.range_succ, List.range'_eq_map_range]
  rw [hsplit, List.filter_append, List.filter_cons_of_pos (by simpa using hp)]
  refine ⟨by simp, ?_⟩
  rw [List.getElem_append_right (by simp)]
  simp

/-- **Forward:** the code S4 assigns symbol `i` decodes, at its length, to `i`. -/
theorem lookup_codeOf (lens : Array Nat) (i : Nat) (hi : i < lens.size)
    (hl0 : lens.getD i 0 ≠ 0) (hl : lens.getD i 0 < 16) :
    lookup (assign lens) (lens.getD i 0) (codeOf lens i) = some i := by
  obtain ⟨hlt, hget⟩ := filter_range_at (fun j => lens.getD j 0 = lens.getD i 0) lens.size i hi rfl
  unfold lookup codeOf
  rw [assign_count _ _ hl, assign_syms _ _ hl, assign_first, blCount_eq _ _ hl0, symsOf_eq]
  have hlt' : ((List.range i).filter (fun j => lens.getD j 0 = lens.getD i 0)).length < (symsL lens (lens.getD i 0)).length := hlt
  rw [if_pos ⟨by omega, by omega⟩]
  simp only [Nat.add_sub_cancel_left, Array.getD, List.size_toArray, hlt', dite_true, List.getElem_toArray]
  exact congrArg some hget

theorem symsL_nodup (lens : Array Nat) (l : Nat) : (symsL lens l).Nodup :=
  (List.nodup_range).filter _

/-- **Converse:** a value that decodes at length ℓ to `i` is exactly the code S4 assigns `i`, and `i` has length ℓ. -/
theorem lookup_some (lens : Array Nat) (l v i : Nat) (hl0 : l ≠ 0) (hl : l < 16)
    (h : lookup (assign lens) l v = some i) :
    i < lens.size ∧ lens.getD i 0 = l ∧ v = codeOf lens i := by
  unfold lookup at h
  rw [assign_count _ _ hl, assign_syms _ _ hl, assign_first, blCount_eq _ _ hl0, symsOf_eq] at h
  split_ifs at h with hr
  obtain ⟨hr1, hr2⟩ := hr
  have hk : v - (nextCodes lens).getD l 0 < (symsL lens l).length := by omega
  simp only [Array.getD, List.size_toArray, hk, dite_true, List.getElem_toArray, Option.some.injEq] at h
  have hmem : i ∈ symsL lens l := h ▸ List.getElem_mem hk
  simp only [symsL, List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
  obtain ⟨hi, hli⟩ := hmem
  refine ⟨hi, hli, ?_⟩
  obtain ⟨hlt, hget⟩ := filter_range_at (fun j => lens.getD j 0 = l) lens.size i hi hli
  have hrank : ((List.range i).filter (fun j => lens.getD j 0 = l)).length = v - (nextCodes lens).getD l 0 :=
    (symsL_nodup lens l).getElem_inj_iff.mp (hget.trans h.symm : _)
  unfold codeOf
  rw [hli, hrank]
  omega

end VIRDeflate.MutRev
