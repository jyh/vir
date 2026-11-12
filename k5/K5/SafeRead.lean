/-
  O95, K5-2b PILOT (k5/RANGE-SITES.md): READ's range obligations discharged at the Safety level, from Inv alone (no Mag: every
  cell READ's arithmetic reads is bounded by Inv), with n < 2³². The facts are taken exactly as Safety's `safeI_read` takes them.
-/
import K5.Modes4
import VIRDeflate.Safety

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

theorem pow_le_65536 {k : Nat} (h : 2 ^ k ≤ 65536) : k ≤ 16 := by
  by_contra hk
  have : 2 ^ 17 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem kcap_le (md : Int) : kcap md ≤ 65536 := by
  unfold kcap; split_ifs <;> norm_num

/-- **READ is in range** on every world satisfying Safety's invariant, for n < 2³². -/
theorem read_inR {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mREAD) :
    SrcInRange (closeAt p readT, σ) := by
  have hL : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  by_cases hlt : f cBY < b.size
  · obtain ⟨hfr, hk1, hw1, ha0, hal, hcap⟩ := hi.2.read hm
    obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have ht01 := hi.1.bits (8 * (b[(f cBY).toNat]'(by omega) : Int) + f cBI) (by omega) (by omega) (Or.inl hnt)
    set t := f (BT + (8 * (b[(f cBY).toNat]'(by omega) : Int) + f cBI)) with ht
    have hcap' : f cWT * 2 ^ (f cK).toNat ≤ 65536 := le_trans hcap (kcap_le _)
    have hp1 : (1 : Int) ≤ 2 ^ (f cK).toNat := by exact_mod_cast Nat.one_le_two_pow
    have hwt : f cWT ≤ 65536 := by nlinarith
    have hk16 : (f cK).toNat ≤ 16 := by
      apply pow_le_65536
      have : (2 : Int) ^ (f cK).toNat ≤ 65536 := by nlinarith
      exact_mod_cast this
    have ht2 : t = 0 ∨ t = 1 := ht01
    have r7 : inRange (t * f cWT) = true := by
      rcases ht2 with h | h <;> rw [h] <;> apply inRange_eq <;> nlinarith
    have r8 : inRange (f cACC + t * f cWT) = true := by
      rcases ht2 with h | h <;> rw [h] <;> apply inRange_eq <;> nlinarith
    have r9 : inRange (2 * f cWT) = true := inRange_eq (by omega) (by omega)
    have r10 : inRange (f cK - 1) = true := inRange_eq (by omega) (by omega)
    exact readbit_inR hw (f cBY).toNat (f cBI).toNat b.size (b[(f cBY).toNat]'(by omega)) (f cK) (f cACC) (f cWT)
      (f cRET) t hL hn32 (by omega) (by omega) hn (by omega) (by omega) hv hv8 (by rw [hbiE]) rfl rfl rfl rfl r7 r8 r9 r10
  · exact readbit_trunc_inR hw (by unfold L0; omega) (f cBY) b.size rfl hn (by omega)

end K5
