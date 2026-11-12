import VIRDeflate.Step
#check @List.idxOf_cons
#check @List.idxOf_nil
#check @List.idxOf_append
example (x y : String) (l : List String) : List.idxOf x (y :: l) = if y == x then 0 else List.idxOf x l + 1 := by
  simp [List.idxOf_cons]
