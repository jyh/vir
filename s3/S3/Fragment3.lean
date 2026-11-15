/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 16): `Fragment3.ok`, the static premises of `compile_x86` about the code
  as ONE Bool, and its soundness. Leaves out `1 ≤ ilen` (a fact about the encoder length) and the disp32 encoding clause (S4's).
-/
import S3.Cross3

namespace S3
open VIRC X86

/-- S3's static check on a lowered program: code under 2⁶⁴ bytes, table under 2⁶⁴ entries, every code's BUF demand within N. -/
def Fragment3.ok (ilen : X86.Op → Nat) (tbl : Table) (main : WCode) (base : W) (N : Nat) : Bool :=
  decide (bytes (ctxOf ilen tbl main base) (allCode (ctxOf ilen tbl main base) tbl main) < 2 ^ 64) &&
  decide (tbl.length < 2 ^ 64) && decide (needW main ≤ N) && tbl.all (fun e => decide (needW e.2 ≤ N))

/-- **fragment3_sound.** A true `Fragment3.ok` gives the four static premises `s3_refines_from_s2` / `compile_x86` take. -/
theorem fragment3_sound {ilen : X86.Op → Nat} {tbl : Table} {main : WCode} {base : W} {N : Nat}
    (h : Fragment3.ok ilen tbl main base N = true) :
    bytes (ctxOf ilen tbl main base) (allCode (ctxOf ilen tbl main base) tbl main) < 2 ^ 64 ∧ tbl.length < 2 ^ 64 ∧
      needW main ≤ N ∧ ∀ e ∈ tbl, needW e.2 ≤ N := by
  simp only [Fragment3.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end S3
