import K5.InRange
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step
example (p m : Int) (H : Finmap (fun _ : Int => Int)) (e : (H.insert (p + 0) 5).lookup (p + cMODE) = some m) : m = 5 := by
  rw [show p + cMODE = p + 0 from rfl, Finmap.lookup_insert] at e
  exact (Option.some.inj e).symm
example (p m : Int) (H : Finmap (fun _ : Int => Int)) (e : ((H.insert (p + 10) 0).insert (p + 0) 6).lookup (p + cMODE) = some m) : m = 6 := by
  rw [show p + cMODE = p + 0 from rfl, Finmap.lookup_insert] at e
  exact (Option.some.inj e).symm
