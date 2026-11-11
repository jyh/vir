/-
OBJECT-DEFLATE, Appendix S §S2–S3, S5–S8 as an executable Lean spec (X4 (a): the arm formalizes THESE bytes).

TWO READINGS, by errata/ERRATA-DEFLATE.md row DEFLATE-E1 (recorded before this file was built):
* `inflateLit` — S read literally: S5's fixed codes go through S4's `code`, completeness REJECTs included. FIXED_D
  (30 symbols of length 5) is incomplete, so every fixed-Huffman block REJECTs "incomplete".
* `inflate` — the repaired reading: S5's fixed codes are S4's assignment with no completeness check; every other clause is
  shared, byte for byte, through the same functions.

LOOPS. S's `repeat … until`, `while` and `loop` are written with a fuel argument set at entry to the number of input bits not
yet read, plus one. Every iteration of each of those loops reads at least one bit (a block header, a `decode`), and `bit`
REJECTs "truncated" when no bit remains, so the fuel cannot run out before a REJECT; running out REJECTs "truncated". That
claim is a lemma OWED (it is not proved here), and it is the only place the fuel can differ from S.
-/
import VIRDeflate.Huffman

namespace VIRDeflate.MutB0

/-- Bits not yet read, plus one: the fuel for a loop entered now. -/
def fuelNow : M Nat := do
  let e ← read
  let s ← get
  return 8 * e.inp.size - s.pos + 1

/-- S3: `stored()`. -/
def stored : M Unit := do
  align
  let len ← bits 16
  let nlen ← bits 16
  if nlen ≠ len ^^^ 0xFFFF then reject "invalid stored block lengths"
  let e ← read
  let s ← get
  if s.pos / 8 + len > e.inp.size then reject "truncated"
  if s.out.size + len > e.outmax then reject "overflow"
  set ({ pos := s.pos + 8 * len, out := s.out ++ e.inp.extract (s.pos / 8) (s.pos / 8 + len) } : St)

/-- S5: the fixed literal/length lengths: 0..143 → 8, 144..255 → 9, 256..279 → 7, 280..287 → 8. -/
def fixedLLens : Array Nat :=
  (List.range 288).toArray.map fun i => if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8

/-- S5: the fixed distance lengths: 0..29 → 5 (30 symbols). -/
def fixedDLens : Array Nat := (List.range 30).toArray.map fun _ => 5

/-- S7's tables. -/
def LBASE : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163,
  195, 227, 258]
def LEXTRA : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
def DBASE : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049,
  3073, 4097, 6145, 8193, 12289, 16385, 24577]
def DEXTRA : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

/-- S7's copy, ONE BYTE AT A TIME: `append o[m - dist] to o`, `len` times (overlap repeats, §3.2.3). -/
def copyBack (dist : Nat) : Nat → Array Nat → Array Nat
  | 0, o => o
  | k + 1, o => copyBack dist k (o.push (o.getD (o.size - dist) 0))

/-- S7: `huff(L, D)`'s loop. -/
def huffLoop (L D : Code) : Nat → M Unit
  | 0 => reject "truncated"
  | fuel + 1 => do
    let s ← decode L
    if s < 256 then
      let e ← read
      let st ← get
      if st.out.size = e.outmax then reject "overflow"
      set { st with out := st.out.push s }
      huffLoop L D fuel
    else if s = 256 then
      return ()
    else if s ≤ 285 then
      let len := LBASE.getD (s - 257) 0 + (← bits (LEXTRA.getD (s - 257) 0))
      let d ← decode D
      if d ≥ 30 then reject "invalid distance code"
      let dist := DBASE.getD d 0 + (← bits (DEXTRA.getD d 0))
      let e ← read
      let st ← get
      if dist > st.out.size then reject "distance too far back"
      if st.out.size + len > e.outmax then reject "overflow"
      set { st with out := copyBack dist len st.out }
      huffLoop L D fuel
    else
      reject "invalid literal/length code"

/-- S7: `huff(L, D)`. -/
def huff (L D : Code) : M Unit := do huffLoop L D (← fuelNow)

/-- S6: the ORDER of the code-length code's lengths. -/
def ORDER : List Nat := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- S6: `cl[ORDER[i]] := bits(3) for i < HCLEN`; the rest stay 0. -/
def readCL : List Nat → Nat → Array Nat → M (Array Nat)
  | [], _, cl => pure cl
  | o :: os, k, cl =>
    if k = 0 then pure cl else do
      let x ← bits 3
      readCL os (k - 1) (cl.set! o x)

/-- Append `x` to `a`, `k` times. -/
def pushN (x : Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => pushN x k (a.push x)

/-- S6: the `while |lens| < HLIT + HDIST` loop. -/
def lensLoop (CL : Code) (total : Nat) : Nat → Array Nat → M (Array Nat)
  | 0, _ => reject "truncated"
  | fuel + 1, lens =>
    if lens.size < total then do
      let s ← decode CL
      let lens' ←
        if s ≤ 15 then pure (lens.push s)
        else if s = 16 then do
          if lens.size = 0 then reject "repeat with no first length"
          let r ← bits 2
          pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens)
        else if s = 17 then do
          let r ← bits 3
          pure (pushN 0 (3 + r) lens)
        else do
          let r ← bits 7
          pure (pushN 0 (11 + r) lens)
      if lens'.size > total then reject "invalid bit length repeat"
      lensLoop CL total fuel lens'
    else
      pure lens

/-- S6: `dynamic()`. -/
def dynamic : M Unit := do
  let hlit := (← bits 5) + 257
  let hdist := (← bits 5) + 1
  let hclen := (← bits 4) + 4
  if hlit > 286 ∨ hdist > 30 then reject "too many length or distance symbols"
  let cl ← readCL ORDER hclen (Array.replicate 19 0)
  let CL ← code cl .strict
  let lens ← lensLoop CL (hlit + hdist) (← fuelNow) #[]
  if lens.getD 256 0 = 0 then reject "missing end-of-block"
  let L ← code (lens.extract 0 hlit)
  let D ← code (lens.extract hlit (hlit + hdist)) .dist
  huff L D

/-- S5's fixed codes, by reading: `lit = true` is S read literally (through `code`, checks included — DEFLATE-E1);
`lit = false` is the repaired reading (S4's assignment alone). -/
def fixedCodes (lit : Bool) : M (Code × Code) :=
  if lit then do
    let L ← code fixedLLens
    let D ← code fixedDLens
    pure (L, D)
  else
    pure (assign fixedLLens, assign fixedDLens)

/-- S2: the block loop, `repeat … until BFINAL = 1`. -/
def blocks (lit : Bool) : Nat → M Unit
  | 0 => reject "truncated"
  | fuel + 1 => do
    let bfinal ← bits 0
    let btype ← bits 2
    if btype = 0 then stored
    else if btype = 1 then do
      let (L, D) ← fixedCodes lit
      huff L D
    else if btype = 2 then dynamic
    else reject "invalid block type"
    if bfinal = 1 then return () else blocks lit fuel

/-- Run the spec on input `b` with bound `outmax`: `.ok o` is ACCEPT o, `.error r` is `reject(r)` (S8). -/
def run (lit : Bool) (b : Array Nat) (outmax : Nat) : Except String (Array Nat) :=
  match ((do blocks lit (← fuelNow) : M Unit).run ⟨b, outmax⟩).run ⟨0, #[]⟩ with
  | .ok (_, s) => .ok s.out
  | .error r => .error r

/-- S read literally (DEFLATE-E1's first reading). -/
def inflateLit (b : Array Nat) (outmax : Nat) : Except String (Array Nat) := run true b outmax

/-- The repaired reading (DEFLATE-E1's decision). -/
def inflate (b : Array Nat) (outmax : Nat) : Except String (Array Nat) := run false b outmax

/-! ## Fuel adequacy (STAGE-DEFLATE limit (a), STATUS-vir 289 (a))

S's loops have no bound; ours take fuel = unread bits + 1 at entry. The claim: every iteration reads at least one bit, so more
fuel never changes a result. It is stated per loop as FUEL ADEQUACY (`huffLoop_fuel`, `lensLoop_fuel`, `blocks_fuel`): from any
state, any two fuels above the unread bits give the same run. It rests on two progress classes. `Mono` never moves the bit
position back. `Adv` moves it strictly forward, from a position inside the input. -/

section Fuel

variable {α β : Type}

/-- Running an action from an environment and a state. -/
def go (m : M α) (e : Env) (s : St) : Except String (α × St) := (m.run e).run s

theorem go_bind (m : M α) (k : α → M β) (e : Env) (s : St) :
    go (m >>= k) e s = (match go m e s with
      | .ok (a, s') => go (k a) e s'
      | .error r => .error r) := by
  unfold go
  show (do let p ← m e s; k p.1 e p.2 : Except String (β × St)) =
    (match m e s with
      | .ok (a, s') => k a e s'
      | .error r => .error r)
  cases m e s with
  | error r => rfl
  | ok p => obtain ⟨a, s'⟩ := p; rfl

theorem go_pure (a : α) (e : Env) (s : St) : go (pure a : M α) e s = .ok (a, s) := rfl
theorem go_reject (r : String) (e : Env) (s : St) : go (reject r : M α) e s = .error r := rfl
theorem go_read (e : Env) (s : St) : go (read : M Env) e s = .ok (e, s) := rfl
theorem go_get (e : Env) (s : St) : go (get : M St) e s = .ok (s, s) := rfl
theorem go_set (t : St) (e : Env) (s : St) : go (set t : M PUnit) e s = .ok (⟨⟩, t) := rfl
theorem go_fuelNow (e : Env) (s : St) : go fuelNow e s = .ok (8 * e.inp.size - s.pos + 1, s) := rfl

/-- Never moves the bit position back. -/
def Mono (m : M α) : Prop := ∀ e s a s', go m e s = .ok (a, s') → s.pos ≤ s'.pos

/-- Moves the bit position strictly forward, from a position inside the input. -/
def Adv (m : M α) : Prop := ∀ e s a s', go m e s = .ok (a, s') → s.pos < s'.pos ∧ s.pos < 8 * e.inp.size

theorem Adv.mono {m : M α} (h : Adv m) : Mono m := fun e s a s' hg => Nat.le_of_lt (h e s a s' hg).1

theorem mono_pure (a : α) : Mono (pure a : M α) := by
  intro e s b s' hg; rw [go_pure] at hg; cases hg; exact le_rfl

theorem adv_reject (r : String) : Adv (reject r : M α) := by
  intro e s b s' hg; rw [go_reject] at hg; cases hg

theorem mono_reject (r : String) : Mono (reject r : M α) := (adv_reject r).mono

theorem mono_bind {m : M α} {k : α → M β} (hm : Mono m) (hk : ∀ a, Mono (k a)) : Mono (m >>= k) := by
  intro e s b s' hg
  rw [go_bind] at hg
  split at hg
  · rename_i a s1 h1
    exact le_trans (hm e s a s1 h1) (hk a e s1 b s' hg)
  · cases hg

theorem adv_bind_l {m : M α} {k : α → M β} (hm : Adv m) (hk : ∀ a, Mono (k a)) : Adv (m >>= k) := by
  intro e s b s' hg
  rw [go_bind] at hg
  split at hg
  · rename_i a s1 h1
    obtain ⟨p1, i1⟩ := hm e s a s1 h1
    exact ⟨lt_of_lt_of_le p1 (hk a e s1 b s' hg), i1⟩
  · cases hg

theorem adv_bind_r {m : M α} {k : α → M β} (hm : Mono m) (hk : ∀ a, Adv (k a)) : Adv (m >>= k) := by
  intro e s b s' hg
  rw [go_bind] at hg
  split at hg
  · rename_i a s1 h1
    have p1 := hm e s a s1 h1
    obtain ⟨p2, i2⟩ := hk a e s1 b s' hg
    exact ⟨lt_of_le_of_lt p1 p2, lt_of_le_of_lt p1 i2⟩
  · cases hg

theorem mono_ite {c : Prop} [Decidable c] {t f : M α} (ht : Mono t) (hf : Mono f) : Mono (if c then t else f) := by
  split <;> assumption

theorem mono_read : Mono (read : M Env) := by
  intro e s a s' hg; rw [go_read] at hg; cases hg; exact le_rfl

theorem mono_get : Mono (get : M St) := by
  intro e s a s' hg; rw [go_get] at hg; cases hg; exact le_rfl

theorem mono_fuelNow : Mono fuelNow := by
  intro e s a s' hg; rw [go_fuelNow] at hg; cases hg; exact le_rfl

theorem adv_bit : Adv bit := by
  intro e s a s' hg
  unfold bit at hg
  simp only [go_bind, go_read, go_get] at hg
  split_ifs at hg with h
  · rw [go_bind, go_set] at hg
    simp only [go_pure] at hg
    cases hg
    refine ⟨by simp, by omega⟩
  · rw [go_reject] at hg; cases hg

theorem mono_bitsGo (j i acc : Nat) : Mono (bitsGo j i acc) := by
  induction j generalizing i acc with
  | zero => exact mono_pure _
  | succ j ih => exact (adv_bind_l adv_bit fun x => ih _ _).mono

theorem mono_bits (k : Nat) : Mono (bits k) := mono_bitsGo _ _ _

theorem adv_bits (k : Nat) : Adv (bits (k + 1)) := adv_bind_l adv_bit fun _ => mono_bitsGo _ _ _

theorem mono_align : Mono align := by
  intro e s a s' hg
  cases hg
  show s.pos ≤ 8 * ((s.pos + 7) / 8)
  omega

theorem adv_decodeGo (C : Code) (f l v : Nat) : Adv (decodeGo C f l v) := by
  induction f generalizing l v with
  | zero => exact adv_reject _
  | succ f ih =>
    exact adv_bind_l adv_bit fun x => mono_ite (mono_pure _) (ih _ _).mono

theorem adv_decode (C : Code) : Adv (decode C) := adv_decodeGo _ _ _ _

/-- `code` does not touch the state. -/
theorem mono_code (lens : Array Nat) (mode : Mode) : Mono (code lens mode) := by
  unfold code
  split
  · exact mono_reject _
  · exact mono_ite (mono_reject _) (mono_pure _)

/-! ### Start-state-relative progress (`MF`): it keeps the fact that `get` returns the current state, which is what a `set`
needs. `Mono m` is `MF e st m` for every `e` and `st`, by definition. -/

def MF (e : Env) (st : St) (m : M α) : Prop := ∀ a s', go m e st = .ok (a, s') → st.pos ≤ s'.pos

theorem mf_bind {m : M α} {k : α → M β} {e : Env} {st : St} (hm : Mono m)
    (hk : ∀ a s1, go m e st = .ok (a, s1) → MF e s1 (k a)) : MF e st (m >>= k) := by
  intro b s' hg; rw [go_bind] at hg; split at hg
  · rename_i a s1 h1; exact le_trans (hm e st a s1 h1) (hk a s1 h1 b s' hg)
  · cases hg

theorem mf_get {k : St → M α} {e : Env} {st : St} (h : MF e st (k st)) : MF e st (get >>= k) := by
  intro b s' hg; rw [go_bind, go_get] at hg; exact h b s' hg

theorem mf_read {k : Env → M α} {e : Env} {st : St} (h : MF e st (k e)) : MF e st (read >>= k) := by
  intro b s' hg; rw [go_bind, go_read] at hg; exact h b s' hg

theorem mf_set_bind {k : PUnit → M α} {e : Env} {st t : St} (ht : st.pos ≤ t.pos) (h : MF e t (k ⟨⟩)) :
    MF e st (set t >>= k) := by
  intro b s' hg; rw [go_bind, go_set] at hg; exact le_trans ht (h b s' hg)

theorem mf_set {e : Env} {st t : St} (ht : st.pos ≤ t.pos) : MF e st (set t : M PUnit) := by
  intro b s' hg; rw [go_set] at hg; cases hg; exact ht

theorem mf_pure {e : Env} {st : St} (a : α) : MF e st (pure a : M α) := mono_pure a e st

theorem mf_reject {e : Env} {st : St} (r : String) : MF e st (reject r : M α) := mono_reject r e st

theorem mf_reject_bind {k : α → M β} {e : Env} {st : St} (r : String) : MF e st (reject r >>= k) := by
  intro b s' hg; rw [go_bind, go_reject] at hg; cases hg

theorem mf_ite {c : Prop} [Decidable c] {t f : M α} {e : Env} {st : St} (ht : c → MF e st t) (hf : ¬c → MF e st f) :
    MF e st (if c then t else f) := by
  split
  · exact ht ‹_›
  · exact hf ‹_›

theorem mono_stored : Mono stored := by
  intro e st
  unfold stored
  try dsimp only
  refine mf_bind mono_align fun _ s0 _ => ?_
  refine mf_bind (mono_bits 16) fun len s1 _ => ?_
  refine mf_bind (mono_bits 16) fun nlen s2 _ => ?_
  refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
  refine mf_read (mf_get ?_)
  refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
  refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
  exact mf_set (Nat.le_add_right _ _)

theorem mono_huffLoop (L D : Code) (f : Nat) : Mono (huffLoop L D f) := by
  induction f with
  | zero => exact mono_reject _
  | succ f ih =>
    intro e st
    simp only [huffLoop]
    try dsimp only
    refine mf_bind (adv_decode L).mono fun x s1 _ => ?_
    refine mf_ite (fun _ => ?_) (fun _ => mf_ite (fun _ => mf_pure _)
      (fun _ => mf_ite (fun _ => ?_) (fun _ => mf_reject _)))
    · refine mf_read (mf_get ?_)
      refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
      exact mf_set_bind le_rfl (ih e _)
    · refine mf_bind (mono_bits _) fun ex s2 _ => ?_
      refine mf_bind (adv_decode D).mono fun d s3 _ => ?_
      refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
      refine mf_bind (mono_bits _) fun dx s4 _ => ?_
      refine mf_read (mf_get ?_)
      refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
      refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
      exact mf_set_bind le_rfl (ih e _)

theorem mono_huff (L D : Code) : Mono (huff L D) :=
  mono_bind mono_fuelNow fun f => mono_huffLoop L D f

theorem mono_readCL (os : List Nat) (k : Nat) (cl : Array Nat) : Mono (readCL os k cl) := by
  induction os generalizing k cl with
  | nil => exact mono_pure _
  | cons o os ih =>
    simp only [readCL]
    exact mono_ite (mono_pure _) (mono_bind (mono_bits 3) fun x => ih _ _)

theorem mono_lensLoop (CL : Code) (total f : Nat) (lens : Array Nat) : Mono (lensLoop CL total f lens) := by
  induction f generalizing lens with
  | zero => exact mono_reject _
  | succ f ih =>
    intro e st
    simp only [lensLoop]
    try dsimp only
    refine mf_ite (fun _ => ?_) (fun _ => mf_pure _)
    refine mf_bind (adv_decode CL).mono fun x s1 _ => ?_
    repeat' (first
      | exact mf_reject_bind _
      | exact ih _ e _
      | refine mf_ite (fun _ => ?_) (fun _ => ?_)
      | refine mf_bind (mono_bits _) fun _ _ _ => ?_
      | refine mf_bind (mono_pure _) fun _ _ _ => ?_)

theorem mono_dynamic : Mono dynamic := by
  intro e st
  unfold dynamic
  try dsimp only
  refine mf_bind (mono_bits 5) fun _ _ _ => ?_
  refine mf_bind (mono_bits 5) fun _ _ _ => ?_
  refine mf_bind (mono_bits 4) fun _ _ _ => ?_
  refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
  refine mf_bind (mono_readCL _ _ _) fun _ _ _ => ?_
  refine mf_bind (mono_code _ _) fun _ _ _ => ?_
  refine mf_bind mono_fuelNow fun _ _ _ => ?_
  refine mf_bind (mono_lensLoop _ _ _ _) fun _ _ _ => ?_
  refine mf_ite (fun _ => mf_reject_bind _) (fun _ => ?_)
  refine mf_bind (mono_code _ _) fun _ _ _ => ?_
  refine mf_bind (mono_code _ _) fun _ _ _ => ?_
  exact mono_huff _ _ _ _

theorem mono_fixedCodes (lit : Bool) : Mono (fixedCodes lit) := by
  unfold fixedCodes
  exact mono_ite (mono_bind (mono_code _ _) fun _ => mono_bind (mono_code _ _) fun _ => mono_pure _) (mono_pure _)

/-! ### Agreement (`Ag`): two runs from one state are equal. -/

def Ag (e : Env) (st : St) (m1 m2 : M α) : Prop := go m1 e st = go m2 e st

theorem ag_bind {m : M α} {k1 k2 : α → M β} {e : Env} {st : St}
    (h : ∀ a s1, go m e st = .ok (a, s1) → Ag e s1 (k1 a) (k2 a)) : Ag e st (m >>= k1) (m >>= k2) := by
  unfold Ag; rw [go_bind, go_bind]; split
  · rename_i a s1 h1; exact h a s1 h1
  · rfl

theorem ag_refl {m : M α} {e : Env} {st : St} : Ag e st m m := rfl

theorem ag_reject_bind {k1 k2 : α → M β} {e : Env} {st : St} (r : String) :
    Ag e st (reject r >>= k1) (reject r >>= k2) := by
  unfold Ag; rw [go_bind, go_bind, go_reject]

theorem ag_ite {c : Prop} [Decidable c] {t1 t2 f1 f2 : M α} {e : Env} {st : St}
    (ht : c → Ag e st t1 t2) (hf : ¬c → Ag e st f1 f2) : Ag e st (if c then t1 else f1) (if c then t2 else f2) := by
  split
  · exact ht ‹_›
  · exact hf ‹_›

theorem ag_get {k1 k2 : St → M α} {e : Env} {st : St} (h : Ag e st (k1 st) (k2 st)) :
    Ag e st (get >>= k1) (get >>= k2) := by
  unfold Ag at h ⊢; rw [go_bind, go_bind, go_get]; exact h

theorem ag_read {k1 k2 : Env → M α} {e : Env} {st : St} (h : Ag e st (k1 e) (k2 e)) :
    Ag e st (read >>= k1) (read >>= k2) := by
  unfold Ag at h ⊢; rw [go_bind, go_bind, go_read]; exact h

theorem ag_set_bind {k1 k2 : PUnit → M α} {e : Env} {st t : St} (h : Ag e t (k1 ⟨⟩) (k2 ⟨⟩)) :
    Ag e st (set t >>= k1) (set t >>= k2) := by
  unfold Ag at h ⊢; rw [go_bind, go_bind, go_set]; exact h

/-- **FUEL ADEQUACY, S7's loop:** any two fuels above the unread bits give the same run. -/
theorem huffLoop_fuel (L D : Code) (f : Nat) : ∀ g e st, 8 * e.inp.size - st.pos < f → f ≤ g →
    go (huffLoop L D g) e st = go (huffLoop L D f) e st := by
  induction f with
  | zero => intro g e st h; omega
  | succ f ih =>
    intro g e st hf hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    show Ag e st _ _
    simp only [huffLoop]
    try dsimp only
    refine ag_bind fun x s1 h1 => ?_
    obtain ⟨p1, i1⟩ := adv_decode L e st x s1 h1
    refine ag_ite (fun _ => ?_) (fun _ => ag_ite (fun _ => ag_refl)
      (fun _ => ag_ite (fun _ => ?_) (fun _ => ag_refl)))
    · refine ag_read (ag_get ?_)
      refine ag_ite (fun _ => ag_reject_bind _) (fun _ => ?_)
      exact ag_set_bind (ih g e _ (by show _ - s1.pos < f; omega) (by omega))
    · refine ag_bind fun ex s2 h2 => ?_
      have p2 := mono_bits _ e s1 ex s2 h2
      refine ag_bind fun d s3 h3 => ?_
      have p3 := (adv_decode D).mono e s2 d s3 h3
      refine ag_ite (fun _ => ag_reject_bind _) (fun _ => ?_)
      refine ag_bind fun dx s4 h4 => ?_
      have p4 := mono_bits _ e s3 dx s4 h4
      refine ag_read (ag_get ?_)
      refine ag_ite (fun _ => ag_reject_bind _) (fun _ => ?_)
      refine ag_ite (fun _ => ag_reject_bind _) (fun _ => ?_)
      exact ag_set_bind (ih g e _ (by show _ - s4.pos < f; omega) (by omega))

/-- **FUEL ADEQUACY, S6's code-length loop.** -/
theorem lensLoop_fuel (CL : Code) (total f : Nat) : ∀ g e st lens, 8 * e.inp.size - st.pos < f → f ≤ g →
    go (lensLoop CL total g lens) e st = go (lensLoop CL total f lens) e st := by
  induction f with
  | zero => intro g e st lens h; omega
  | succ f ih =>
    intro g e st lens hf hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    show Ag e st _ _
    simp only [lensLoop]
    try dsimp only
    refine ag_ite (fun _ => ?_) (fun _ => ag_refl)
    refine ag_bind fun x s1 h1 => ?_
    obtain ⟨p1, i1⟩ := adv_decode CL e st x s1 h1
    repeat' (first
      | exact ag_reject_bind _
      | (exact ih g e _ _ (by omega) (by omega))
      | refine ag_ite (fun _ => ?_) (fun _ => ?_)
      | (refine ag_bind fun _ s2 h2 => ?_; have := mono_bits _ e _ _ s2 h2)
      | (refine ag_bind fun _ s2 h2 => ?_; have := mono_pure _ e _ _ s2 h2))

/-- **FUEL ADEQUACY, S2's block loop.** -/
theorem blocks_fuel (lit : Bool) (f : Nat) : ∀ g e st, 8 * e.inp.size - st.pos < f → f ≤ g →
    go (blocks lit g) e st = go (blocks lit f) e st := by
  induction f with
  | zero => intro g e st h; omega
  | succ f ih =>
    intro g e st hf hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    show Ag e st _ _
    simp only [blocks]
    try dsimp only
    refine ag_bind fun bf s1 h1 => ?_
    obtain ⟨p1, i1⟩ := adv_bits 0 e st bf s1 h1
    refine ag_bind fun bt s2 h2 => ?_
    have p2 := mono_bits 2 e s1 bt s2 h2
    have hrec : ∀ s3 : St, s2.pos ≤ s3.pos →
        Ag e s3 (if bf = 1 then pure () else blocks lit g) (if bf = 1 then pure () else blocks lit f) :=
      fun s3 p3 => ag_ite (fun _ => ag_refl) (fun _ => ih g e s3 (by omega) (by omega))
    refine ag_ite (fun _ => ag_bind fun _ s3 h3 => hrec s3 (mono_stored e s2 _ s3 h3)) (fun _ => ?_)
    refine ag_ite (fun _ => ?_) (fun _ => ag_ite (fun _ => ag_bind fun _ s3 h3 => hrec s3 (mono_dynamic e s2 _ s3 h3))
      (fun _ => ag_reject_bind _))
    refine ag_bind fun LD s3 h3 => ?_
    have p3 := mono_fixedCodes lit e s2 LD s3 h3
    exact ag_bind fun _ s4 h4 => hrec s4 (le_trans p3 (mono_huff _ _ e s3 _ s4 h4))

/-- **S7 as the spec calls it equals the loop at ANY fuel above the unread bits** (so `huff` is S7's unbounded loop). -/
theorem huff_adequate (L D : Code) (e : Env) (st : St) (g : Nat) (hg : 8 * e.inp.size - st.pos < g) :
    go (huff L D) e st = go (huffLoop L D g) e st := by
  unfold huff
  rw [go_bind, go_fuelNow]
  dsimp only
  rcases le_total (8 * e.inp.size - st.pos + 1) g with h | h
  · exact (huffLoop_fuel L D _ g e st (by omega) h).symm
  · exact huffLoop_fuel L D g _ e st hg h

/-- **S2 as `run` calls it equals the block loop at ANY fuel above the input's bits.** -/
theorem run_adequate (lit : Bool) (b : Array Nat) (outmax g : Nat) (hg : 8 * b.size < g) :
    run lit b outmax = (match go (blocks lit g) ⟨b, outmax⟩ ⟨0, #[]⟩ with
      | .ok (_, s) => .ok s.out
      | .error r => .error r) := by
  have key : go (do blocks lit (← fuelNow) : M Unit) ⟨b, outmax⟩ ⟨0, #[]⟩ = go (blocks lit g) ⟨b, outmax⟩ ⟨0, #[]⟩ := by
    rw [go_bind, go_fuelNow]
    dsimp only
    rcases le_total (8 * b.size - 0 + 1) g with h | h
    · exact (blocks_fuel lit _ g _ _ (by simp) h).symm
    · exact blocks_fuel lit g _ _ _ (by simpa using hg) h
  unfold run
  rw [← key]
  rfl

/-- **S6's loop as `dynamic` calls it equals the loop at ANY fuel above the unread bits.** -/
theorem lensLoop_adequate (CL : Code) (total : Nat) (lens : Array Nat) (e : Env) (st : St) (g : Nat)
    (hg : 8 * e.inp.size - st.pos < g) :
    go (fuelNow >>= fun f => lensLoop CL total f lens) e st = go (lensLoop CL total g lens) e st := by
  rw [go_bind, go_fuelNow]
  dsimp only
  rcases le_total (8 * e.inp.size - st.pos + 1) g with h | h
  · exact (lensLoop_fuel CL total _ g e st lens (by omega) h).symm
  · exact lensLoop_fuel CL total g _ e st lens hg h

end Fuel

end VIRDeflate.MutB0
