import K5.Checked
namespace K5
open VIRL1 VIRL2 VIRC
theorem t1 (k : Nat) (h : (2:Int)^k ≤ 64) (h0 : 0 < (2:Int)^k) : inRange (2 * 2^k) = true := inRange_eq (by omega) (by omega)
theorem t2 (x : Int) (h : x ≤ 64) (h0 : 0 < x) : inRange (2 * x) = true := inRange_eq (by omega) (by omega)
theorem t3 : inRange (2 * 64) = true := inRange_eq (by norm_num) (by norm_num)
theorem t4 (x : Int) (h : x ≤ 64) (h0 : 0 < x) : (-9223372036854775808 : Int) ≤ 2 * x := by omega
end K5
