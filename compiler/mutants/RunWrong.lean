import VIRC.Lower2
open VIRC VIRL1 VIRL2
-- red control for the concrete runs: the expected value is WRONG (15, not 14); this file must FAIL to check.
example : (runProg [] (.letE tint (.ret (.prim .add [.const (.int 3), .const (.int 4)]))
    (.ret (.pair (.var 0) (.prim .mul [.var 0, .const (.int 2)])))) [] (fun _ => 0) 10).isDone [7, 15] = true := by decide
