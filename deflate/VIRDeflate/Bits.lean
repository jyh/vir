/-
OBJECT-DEFLATE, Appendix S §S1: the bit reader, and D4's pure recursion over `Int`.

Two halves, kept apart on purpose:
* the SPEC's reader (`bit`, `bits`, `align`), written as S1 writes it, with `>>>` and `&&&` on `Nat`. It is the oracle-side text.
* D4: the bit of a byte as the L2 step program will have to compute it, with what P has: `sub`, `lt`, `mul`, `add` over `Int`
  (OBJECT-DEFLATE, "Declared at the pin": no shift, no bitwise operator in P). `bitAt` is that recursion; `bitAt_eq` says it is
  S1's `(b >> i) & 1` on every byte. The L2 term is written later (Step.lean) and is proved equal to `bitAt`.
-/
import Mathlib.Tactic

namespace VIRDeflate

/-- The reader's environment. X6 (a): the input length and OUTMAX are parameters. Input bytes are `Nat`s in 0..255. -/
structure Env where
  inp : Array Nat
  outmax : Nat

/-- S1's state: `pos_bit` and the output `o`. -/
structure St where
  pos : Nat
  out : Array Nat

/-- The spec's monad: read the environment, thread the state, stop with a REJECT reason (S8). -/
abbrev M := ReaderT Env (StateT St (Except String))

/-- S8: `reject(reason)`. -/
def reject {α : Type} (r : String) : M α := throw r

/-- S1: `bit() = (b[pos_bit / 8] >> (pos_bit mod 8)) & 1 ; pos_bit += 1`, REJECT "truncated" if `pos_bit / 8 ≥ n`. -/
def bit : M Nat := do
  let e ← read
  let s ← get
  if s.pos / 8 < e.inp.size then
    set { s with pos := s.pos + 1 }
    return (e.inp.getD (s.pos / 8) 0 >>> (s.pos % 8)) &&& 1
  else
    reject "truncated"

/-- `bits` as a loop: `j` bits still to read, `i` the index of the next one, `acc` the sum so far. -/
def bitsGo : Nat → Nat → Nat → M Nat
  | 0, _, acc => pure acc
  | j + 1, i, acc => do
    let x ← bit
    bitsGo j (i + 1) (acc + x * 2 ^ i)

/-- S1: `bits(k) = Σ_{i<k} bit_i · 2^i`, least-significant bit first. -/
def bits (k : Nat) : M Nat := bitsGo k 0 0

/-- S1: `align() = pos_bit := 8 · ⌈pos_bit / 8⌉`. -/
def align : M Unit := modify fun s => { s with pos := 8 * ((s.pos + 7) / 8) }

/-! ## D4: the bit of a byte by a pure recursion over `Int` (sub, lt, add, mul only) -/

/-- `2^k` by multiplication. -/
def pow2 : Nat → Int
  | 0 => 1
  | k + 1 => 2 * pow2 k

/-- `stripTop n i v` removes bits `i+n, …, i+1` of `v` (high first), by one compare and at most one subtraction each. -/
def stripTop : Nat → Nat → Int → Int
  | 0, _, v => v
  | n + 1, i, v =>
    let p := pow2 (i + n + 1)
    stripTop n i (if v < p then v else v - p)

/-- D4: bit `i` of a byte `v`, for `i ≤ 7`: strip bits 7..i+1, then one compare. -/
def bitAt (v : Int) (i : Nat) : Int :=
  if stripTop (7 - i) i v < pow2 i then 0 else 1

theorem pow2_eq (k : Nat) : pow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow2, ih, pow_succ, mul_comm]

/-- The recursion computes the remainder modulo `2^(i+1)` on its range. -/
theorem stripTop_eq (n i : Nat) (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ (i + n + 1)) :
    stripTop n i v = v % 2 ^ (i + 1) := by
  induction n generalizing v with
  | zero =>
    simp only [stripTop]
    rw [Int.emod_eq_of_lt h0 (by simpa using h1)]
  | succ n ih =>
    simp only [stripTop, pow2_eq]
    have hp : (2 : Int) ^ (i + (n + 1) + 1) = 2 ^ (i + n + 1) * 2 := by
      rw [show i + (n + 1) + 1 = (i + n + 1) + 1 by omega, pow_succ]
    split_ifs with hv
    · exact ih v h0 hv
    · have hge : (2 : Int) ^ (i + n + 1) ≤ v := by omega
      rw [ih (v - 2 ^ (i + n + 1)) (by omega) (by rw [hp] at h1; omega)]
      have hd : (2 : Int) ^ (i + n + 1) = 2 ^ n * 2 ^ (i + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hd, sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right]

/-- **D4's lemma**: on every byte, the `Int` recursion is S1's `(b >> i) & 1`. -/
theorem bitAt_eq (b i : Nat) (hb : b < 256) (hi : i < 8) :
    bitAt (b : Int) i = (((b >>> i) &&& 1 : Nat) : Int) := by
  unfold bitAt
  have h1 : (b : Int) < 2 ^ (i + (7 - i) + 1) := by
    rw [show i + (7 - i) + 1 = 8 by omega]; push_cast; omega
  rw [stripTop_eq (7 - i) i (b : Int) (by positivity) h1, pow2_eq]
  -- over Nat: b % 2^(i+1) = b % 2^i + 2^i * (b / 2^i % 2)
  have hmod : (b : Int) % 2 ^ (i + 1) = ((b % 2 ^ (i + 1) : Nat) : Int) := by
    first | norm_cast | (push_cast; ring)
  rw [hmod, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hs : b % 2 ^ (i + 1) = b % 2 ^ i + 2 ^ i * (b / 2 ^ i % 2) := Nat.mod_pow_succ
  have hlt : ((b % 2 ^ i : Nat) : Int) < 2 ^ i := by exact_mod_cast Nat.mod_lt _ (by positivity)
  have hnn : (0 : Int) ≤ ((b % 2 ^ i : Nat) : Int) := by positivity
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with h | h
  · rw [hs, h]
    generalize b % 2 ^ i = r at hlt hnn ⊢
    push_cast
    split_ifs with hc
    · rfl
    · exfalso; apply hc; linarith
  · rw [hs, h]
    generalize b % 2 ^ i = r at hlt hnn ⊢
    push_cast
    split_ifs with hc
    · exfalso; linarith
    · rfl

end VIRDeflate
