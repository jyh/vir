import K5.InRange
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step
example (p m : Int) (H : Finmap (fun _ : Int => Int)) (e : (H.insert (p + 0) 5).lookup (p + cMODE) = some m) : m = 5 := by
  simp [Finmap.lookup_insert, cMODE] at e
  omega
