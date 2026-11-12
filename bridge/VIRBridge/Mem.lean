/-
O95 compiler S3, vir's half (STATUS-vir 286; compiler/DECLARATIONS-S3-bridge.md, written before this file): S2's word memory
(`VIRC.WMem`, one 64-bit word per cell address) against x86lean's byte memory (`X86.Mem` at 5f2231f), a cell read as the 8 bytes
`readN a 8`, little-endian. Proved through x86lean's interface (`read_write_same`, `read_write_ne`, `readN_congr`) and never by
unfolding `Mem.bytes`.
-/
import X86.Memory
import VIRC.Word

namespace VIRBridge
open X86

/-- B-2: the bytes at every live cell address read back the word memory's word. -/
def Rep (wm : VIRC.WMem) (m : Mem) (S : VIRC.W → Prop) : Prop := ∀ a, S a → m.readN a 8 = wm a

/-- The 8-byte spans at a and a' do not meet. -/
def Apart (a a' : BitVec 64) : Prop := ∀ i j : Nat, i < 8 → j < 8 → a + BitVec.ofNat 64 i ≠ a' + BitVec.ofNat 64 j

/-- B-3's premise: distinct live cells have disjoint spans. -/
def Sep (S : VIRC.W → Prop) : Prop := ∀ a a', S a → S a' → a ≠ a' → Apart a a'

/-- A store of n bytes from a leaves every byte outside its span. -/
theorem writeN_frame (m : Mem) (a b v : BitVec 64) : ∀ n : Nat, (∀ j : Nat, j < n → a + BitVec.ofNat 64 j ≠ b) →
    (m.writeN a v n).read b = m.read b
  | 0, _ => rfl
  | n + 1, h => by
    show ((m.write a (v.setWidth 8)).writeN (a + 1) (v >>> 8) n).read b = m.read b
    rw [writeN_frame _ (a + 1) b (v >>> 8) n (fun j hj e => h (j + 1) (by omega) (by rw [← e]; bv_omega))]
    exact Mem.read_write_ne _ _ _ _ (fun e => h 0 (by omega) (by rw [e]; bv_omega))

/-- Inside its span (n ≤ 8), a store of n bytes reads back byte k of the value at a + k. -/
theorem writeN_in (m : Mem) : ∀ (n : Nat) (a v : BitVec 64) (k : Nat), k < n → n ≤ 8 →
    (m.writeN a v n).read (a + BitVec.ofNat 64 k) = (v >>> (8 * k)).setWidth 8
  | 0, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, v, k, hk, hn => by
    show ((m.write a (v.setWidth 8)).writeN (a + 1) (v >>> 8) n).read (a + BitVec.ofNat 64 k) = _
    cases k with
    | zero =>
      rw [writeN_frame _ (a + 1) _ (v >>> 8) n (fun j hj e => by bv_omega),
        show a + BitVec.ofNat 64 0 = a by simp, Mem.read_write_same]
      simp
    | succ k =>
      rw [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by bv_omega,
        writeN_in _ n (a + 1) (v >>> 8) k (by omega) (by omega), ← BitVec.shiftRight_add]
      congr 2; omega

/-- A read of n bytes from a memory whose bytes at a + k are v's byte k: v's low 8n bits. -/
theorem readN_bytes (m : Mem) : ∀ (n : Nat) (a v : BitVec 64),
    (∀ k : Nat, k < n → m.read (a + BitVec.ofNat 64 k) = (v >>> (8 * k)).setWidth 8) →
    ∀ i : Nat, (m.readN a n).getLsbD i = (decide (i < 8 * n) && v.getLsbD i)
  | 0, _, _, _, i => by simp [Mem.readN]
  | n + 1, a, v, h, i => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.add_zero] at h0
    have ih := readN_bytes m n (a + 1) (v >>> 8) (fun k hk => by
      rw [show a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) by bv_omega, h (k + 1) (by omega),
        ← BitVec.shiftRight_add]
      congr 2; omega)
    show (((m.readN (a + 1) n) <<< 8) ||| (m.read a).setWidth 64).getLsbD i = _
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, h0, BitVec.getLsbD_setWidth]
    by_cases hi : i < 8
    · simp [hi, show i < 64 by omega, show i < 8 * (n + 1) by omega]
    · rw [ih (i - 8), BitVec.getLsbD_ushiftRight, show 8 + (i - 8) = i by omega]
      by_cases h64 : i < 64
      · simp [hi, h64, show (i - 8 < 8 * n) ↔ (i < 8 * (n + 1)) by omega]
      · simp [hi, h64, BitVec.getLsbD_of_ge v i (by omega)]

/-- **B-3 (1), the round trip:** a cell written as 8 bytes reads back the word. -/
theorem readN_writeN (m : Mem) (a v : BitVec 64) : (m.writeN a v 8).readN a 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [readN_bytes _ 8 a v (fun k hk => writeN_in m 8 a v k hk (le_refl _)) i]
  simp [show i < 8 * 8 by omega]

/-- **B-3 (2), a disjoint store:** a cell whose span the store's does not meet reads as before. -/
theorem readN_writeN_apart (m : Mem) (a a' v : BitVec 64) (h : Apart a a') :
    (m.writeN a v 8).readN a' 8 = m.readN a' 8 :=
  Mem.readN_congr _ _ a' 8 (fun i hi => writeN_frame m a _ v 8 (fun j hj e => h j i hj hi e))

/-- **B-3 (3), a store keeps the representation** when distinct live cells are apart. -/
theorem Rep.store {wm : VIRC.WMem} {m : Mem} {S : VIRC.W → Prop} (hR : Rep wm m S) (hS : Sep S) {a : VIRC.W}
    (ha : S a) (v : VIRC.W) : Rep (Function.update wm a v) (m.writeN a v 8) S := by
  intro a' ha'
  by_cases e : a' = a
  · subst e; rw [Function.update_self]; exact readN_writeN m a' v
  · rw [Function.update_of_ne e, readN_writeN_apart m a a' v (hS a a' ha ha' (Ne.symm e))]; exact hR a' ha'

end VIRBridge
