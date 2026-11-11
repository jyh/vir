/-
OBJECT-DEFLATE, Appendix S §S4: the Kraft lemmas. D5's CANONICAL-CODE group (deflate/DECLARATIONS-DEFLATE.md), with Huffman.lean.

`F ℓ = next_code[ℓ] + bl_count[ℓ]` is one past the last ℓ-bit code S4 assigns. Everything below is about F:
* `nextCodes_succ`: S4's loop is `next_code[ℓ+1] = 2·F ℓ`, so `F (ℓ+1) = 2·F ℓ + bl_count[ℓ+1]` and `F ℓ = Σ_{k ≤ ℓ} bl_count[k]·2^(ℓ-k)`.
* OVER-SUBSCRIPTION: S4's `left` after ℓ is `2^ℓ − F ℓ` (`leftAfter_eq`), so S4 rejects "over-subscribed" iff `F 15 > 2^15`,
  i.e. iff the Kraft sum `Σ bl_count[ℓ]·2^-ℓ` exceeds 1 (`oversubscribed_iff`, `F_eq_sum`).
* COMPLETENESS: the `left` S4 tests for "incomplete" is `2^15 − F 15`, so a code is complete iff the Kraft sum is exactly 1.
* DECODE UNIQUENESS: the codes are PREFIX-FREE (`prefix_free`): no proper prefix of a code is a code. With `lookup_some`
  (Huffman.lean), a bit string that `decode` accepts names exactly one symbol, and `decode` stops at the only length it can.
  When the code is not over-subscribed, every code is a genuine ℓ-bit string (`codes_fit`).
-/
import VIRDeflate.Huffman

namespace VIRDeflate

/-- One step of S4's `next_code` loop. -/
def ncStep (lens : Array Nat) (acc : Nat × Array Nat) (l : Nat) : Nat × Array Nat :=
  let c := (acc.1 + blCount lens (l - 1)) <<< 1
  (c, acc.2.push c)

theorem nextCodes_def (lens : Array Nat) : nextCodes lens = ((List.range' 1 15).foldl (ncStep lens) (0, #[0])).2 := rfl

theorem blCount_zero (lens : Array Nat) : blCount lens 0 = 0 := by simp [blCount]

theorem getD_push_lt (a : Array Nat) (x j : Nat) (h : j < a.size) : (a.push x).getD j 0 = a.getD j 0 := by
  simp [Array.getD, h, Nat.lt_succ_of_lt h, Array.getElem_push_lt]

theorem getD_push_eq (a : Array Nat) (x : Nat) : (a.push x).getD a.size 0 = x := by
  simp [Array.getD]

/-- The loop's invariant after lengths 1..k. -/
theorem ncLoop_inv (lens : Array Nat) (k : Nat) :
    let acc := (List.range' 1 k).foldl (ncStep lens) (0, #[0])
    acc.2.size = k + 1 ∧ acc.1 = acc.2.getD k 0 ∧ acc.2.getD 0 0 = 0 ∧
      ∀ j < k, acc.2.getD (j + 1) 0 = 2 * (acc.2.getD j 0 + blCount lens j) := by
  induction k with
  | zero => simp [Array.getD]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ncStep, Nat.one_mul, Nat.add_sub_cancel_left]
    generalize (List.range' 1 k).foldl (ncStep lens) (0, #[0]) = acc at h1 h2 h3 h4
    refine ⟨by simp [h1], ?_, ?_, ?_⟩
    · show _ = (acc.2.push _).getD (k + 1) 0
      rw [← h1, getD_push_eq]
    · rw [getD_push_lt _ _ _ (by omega)]; exact h3
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [getD_push_lt _ _ _ (by omega), getD_push_lt _ _ _ (by omega)]
        exact h4 j hj
      · subst hj
        rw [show j + 1 = acc.2.size by omega, getD_push_eq, getD_push_lt _ _ _ (by omega), ← h2,
          Nat.shiftLeft_eq]
        ring

/-- **S4's `next_code` loop:** `next_code[0] = 0` and `next_code[ℓ+1] = 2·(next_code[ℓ] + bl_count[ℓ])` for ℓ < 15. -/
theorem nextCodes_zero (lens : Array Nat) : (nextCodes lens).getD 0 0 = 0 := (ncLoop_inv lens 15).2.2.1

theorem nextCodes_succ (lens : Array Nat) (j : Nat) (hj : j < 15) :
    (nextCodes lens).getD (j + 1) 0 = 2 * ((nextCodes lens).getD j 0 + blCount lens j) :=
  (ncLoop_inv lens 15).2.2.2 j hj

/-- One past the last ℓ-bit code. -/
def F (lens : Array Nat) (l : Nat) : Nat := (nextCodes lens).getD l 0 + blCount lens l

theorem F_zero (lens : Array Nat) : F lens 0 = 0 := by unfold F; rw [nextCodes_zero, blCount_zero]

theorem F_succ (lens : Array Nat) (j : Nat) (hj : j < 15) : F lens (j + 1) = 2 * F lens j + blCount lens (j + 1) := by
  unfold F; rw [nextCodes_succ lens j hj]

/-- **The Kraft sum:** `F ℓ = Σ_{k ≤ ℓ} bl_count[k]·2^(ℓ-k)`. -/
theorem F_eq_sum (lens : Array Nat) (l : Nat) (hl : l ≤ 15) :
    F lens l = ∑ k ∈ Finset.range (l + 1), blCount lens k * 2 ^ (l - k) := by
  induction l with
  | zero => simp [F_zero, blCount_zero]
  | succ l ih =>
    rw [F_succ lens l (by omega), ih (by omega), Finset.sum_range_succ _ (l + 1), Finset.mul_sum]
    simp only [Nat.sub_self, pow_zero, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show l + 1 - k = (l - k) + 1 by omega, pow_succ]
    ring

theorem F_mono (lens : Array Nat) (j : Nat) (hj : j < 15) : 2 * F lens j ≤ F lens (j + 1) := by
  rw [F_succ lens j hj]; omega

/-- `F` at least doubles per length. -/
theorem F_grow (lens : Array Nat) (l d : Nat) (h : l + d ≤ 15) : 2 ^ d * F lens l ≤ F lens (l + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := F_mono lens (l + d) (by omega)
    rw [pow_succ, show l + (d + 1) = l + d + 1 by omega]
    nlinarith [ih (by omega)]

/-- One step of S4's `left` loop. -/
def leftStep (lens : Array Nat) (acc : Option Int) (l : Nat) : Option Int :=
  match acc with
  | none => none
  | some left =>
    let left' := 2 * left - (blCount lens l : Int)
    if left' < 0 then none else some left'

theorem leftAfter_def (lens : Array Nat) : leftAfter lens = (List.range' 1 15).foldl (leftStep lens) (some 1) := rfl

theorem foldl_leftStep_none (lens : Array Nat) (xs : List Nat) : xs.foldl (leftStep lens) none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [leftStep] using ih

/-- **S4's `left` is `2^ℓ − F ℓ`**, and the loop has rejected iff some `F j > 2^j`. -/
theorem leftLoop_eq (lens : Array Nat) (k : Nat) (hk : k ≤ 15) :
    (List.range' 1 k).foldl (leftStep lens) (some 1) =
      if ∀ j, 1 ≤ j → j ≤ k → F lens j ≤ 2 ^ j then some ((2 : Int) ^ k - F lens k) else none := by
  induction k with
  | zero => simp [F_zero]
  | succ k ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega)]
    have hF := F_succ lens k (by omega)
    by_cases hall : ∀ j, 1 ≤ j → j ≤ k → F lens j ≤ 2 ^ j
    · rw [if_pos hall]
      simp only [List.foldl_cons, List.foldl_nil, leftStep, Nat.one_mul, show 1 + k = k + 1 by omega]
      have hk0 : F lens k ≤ 2 ^ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp [F_zero]
        · exact hall k h0 le_rfl
      have hk0' : (F lens k : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hk0
      have hF' : (F lens (k + 1) : Int) = 2 * (F lens k : Int) + (blCount lens (k + 1) : Int) := by exact_mod_cast hF
      have hp : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by ring
      by_cases hk1 : F lens (k + 1) ≤ 2 ^ (k + 1)
      · have hk1' : (F lens (k + 1) : Int) ≤ (2 : Int) ^ (k + 1) := by exact_mod_cast hk1
        have hall' : ∀ j, 1 ≤ j → j ≤ k + 1 → F lens j ≤ 2 ^ j := by
          intro j h1 h2
          rcases Nat.lt_or_ge j (k + 1) with h | h
          · exact hall j h1 (by omega)
          · rw [show j = k + 1 by omega]; exact hk1
        rw [if_pos hall', if_neg (by omega)]
        congr 1
        rw [hp, hF']
        ring
      · have hk1' : (2 : Int) ^ (k + 1) < (F lens (k + 1) : Int) := by exact_mod_cast Nat.lt_of_not_le hk1
        have hall' : ¬ ∀ j, 1 ≤ j → j ≤ k + 1 → F lens j ≤ 2 ^ j := fun h => hk1 (h (k + 1) (by omega) le_rfl)
        rw [if_neg hall', if_pos (by omega)]
    · rw [if_neg hall, foldl_leftStep_none]
      have hall' : ¬ ∀ j, 1 ≤ j → j ≤ k + 1 → F lens j ≤ 2 ^ j := fun h => hall fun j h1 h2 => h j h1 (by omega)
      rw [if_neg hall']

/-- `F j ≤ 2^j` for every length iff it holds at 15 (F at least doubles). -/
theorem fits_iff (lens : Array Nat) : (∀ j, 1 ≤ j → j ≤ 15 → F lens j ≤ 2 ^ j) ↔ F lens 15 ≤ 2 ^ 15 := by
  constructor
  · intro h; exact h 15 (by norm_num) le_rfl
  · intro h j h1 h2
    have g := F_grow lens j (15 - j) (by omega)
    rw [show j + (15 - j) = 15 by omega] at g
    have : 2 ^ (15 - j) * F lens j ≤ 2 ^ (15 - j) * 2 ^ j := by
      calc 2 ^ (15 - j) * F lens j ≤ 2 ^ 15 := le_trans g h
        _ = 2 ^ (15 - j) * 2 ^ j := by rw [← pow_add, show 15 - j + j = 15 by omega]
    exact Nat.le_of_mul_le_mul_left this (by positivity)

/-- **S4's `left` after the loop.** -/
theorem leftAfter_eq (lens : Array Nat) :
    leftAfter lens = if F lens 15 ≤ 2 ^ 15 then some ((2 : Int) ^ 15 - F lens 15) else none := by
  rw [leftAfter_def, leftLoop_eq lens 15 le_rfl]
  by_cases h : F lens 15 ≤ 2 ^ 15
  · rw [if_pos ((fits_iff lens).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((fits_iff lens).mp h')), if_neg h]

/-- **OVER-SUBSCRIPTION is the Kraft inequality:** S4 rejects "over-subscribed" iff `Σ_{ℓ ≤ 15} bl_count[ℓ]·2^(15-ℓ) > 2^15`,
i.e. iff `Σ bl_count[ℓ]·2^-ℓ > 1`. -/
theorem oversubscribed_iff (lens : Array Nat) :
    leftAfter lens = none ↔ 2 ^ 15 < ∑ k ∈ Finset.range 16, blCount lens k * 2 ^ (15 - k) := by
  rw [leftAfter_eq, ← F_eq_sum lens 15 le_rfl]
  by_cases h : F lens 15 ≤ 2 ^ 15
  · rw [if_pos h]
    exact ⟨fun h' => (by cases h'), fun h' => absurd h (Nat.not_le_of_lt h')⟩
  · rw [if_neg h]
    exact ⟨fun _ => Nat.lt_of_not_le h, fun _ => rfl⟩

/-- **COMPLETENESS is Kraft equality:** S4's `left` is 0 iff `Σ bl_count[ℓ]·2^(15-ℓ) = 2^15`. -/
theorem complete_iff (lens : Array Nat) :
    leftAfter lens = some 0 ↔ ∑ k ∈ Finset.range 16, blCount lens k * 2 ^ (15 - k) = 2 ^ 15 := by
  rw [leftAfter_eq, ← F_eq_sum lens 15 le_rfl]
  have c15 : ((2 : Nat) ^ 15 : Nat) = 32768 := by norm_num
  have c15' : (2 : Int) ^ 15 = 32768 := by norm_num
  rw [c15, c15']
  by_cases h : F lens 15 ≤ 32768
  · rw [if_pos h, Option.some.injEq]
    constructor
    · intro h'; omega
    · intro h'; rw [h']; norm_num
  · rw [if_neg h]
    exact ⟨fun h' => (by cases h'), fun h' => absurd h'.le h⟩

/-- **PREFIX-FREE:** a code at length ℓ₂ never has a code at a shorter length ℓ₁ as its first ℓ₁ bits. -/
theorem prefix_free (lens : Array Nat) (l1 l2 v : Nat) (h12 : l1 < l2) (h2 : l2 < 16)
    (hv : (assign lens).first.getD l2 0 ≤ v) :
    lookup (assign lens) l1 (v / 2 ^ (l2 - l1)) = none := by
  unfold lookup
  rw [if_neg]
  rw [assign_count _ _ (by omega), assign_first]
  rw [assign_first] at hv
  intro ⟨_, hlt⟩
  -- next_code[ℓ₂] = 2·F(ℓ₂ − 1) ≥ 2^(ℓ₂−ℓ₁)·F ℓ₁
  have hstep := nextCodes_succ lens (l2 - 1) (by omega)
  rw [show l2 - 1 + 1 = l2 by omega] at hstep
  have hg := F_grow lens l1 (l2 - 1 - l1) (by omega)
  rw [show l1 + (l2 - 1 - l1) = l2 - 1 by omega] at hg
  have hF2 : F lens (l2 - 1) = (nextCodes lens).getD (l2 - 1) 0 + blCount lens (l2 - 1) := by simp only [F]
  have hF1 : F lens l1 = (nextCodes lens).getD l1 0 + blCount lens l1 := by simp only [F]
  have hpow : 2 ^ (l2 - l1) = 2 * 2 ^ (l2 - 1 - l1) := by
    rw [show l2 - l1 = (l2 - 1 - l1) + 1 by omega, pow_succ]; ring
  have hge : 2 ^ (l2 - l1) * F lens l1 ≤ v := by
    rw [hpow, mul_assoc]; omega
  have hk : 0 < 2 ^ (l2 - l1) := by positivity
  have : F lens l1 ≤ v / 2 ^ (l2 - l1) := (Nat.le_div_iff_mul_le hk).mpr (by rw [mul_comm]; exact hge)
  omega

/-- **CODES FIT** when the code is not over-subscribed: every ℓ-bit code is below `2^ℓ`. -/
theorem codes_fit (lens : Array Nat) (left : Int) (h : leftAfter lens = some left) (l v : Nat) (hl1 : 1 ≤ l) (hl : l < 16)
    (hv : v < (assign lens).first.getD l 0 + (assign lens).count.getD l 0) : v < 2 ^ l := by
  rw [leftAfter_eq] at h
  split_ifs at h with hF
  rw [assign_first, assign_count _ _ hl] at hv
  have := (fits_iff lens).mpr hF l hl1 (by omega)
  unfold F at this
  omega

end VIRDeflate
