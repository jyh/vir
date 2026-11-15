import K7.RouterExits
open VIRL1 VIRL2 VIRL3 K7
set_option maxRecDepth 100000
example : (run₂ 80 (closeW F, wTrunc)).2.H.lookup (0 + 1) = some 1 := rfl
example : (run₂ 80 (closeW F, wEmit)).2.H.lookup (0 + 1) = some 0 := rfl
