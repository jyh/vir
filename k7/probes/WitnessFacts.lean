import K7.Router
import K5.Checked
import VIRL3.Inequality
open VIRL1 VIRL2 VIRL3 VIRC K5
set_option maxRecDepth 100000
example : instL 0 [(Atom.const (.cap 0) : Atom₂)] F = closeW F := rfl
example : σW.R.lookup 0 = some 87 := rfl
example : (run₂ 80 (closeW F, σW)).1 = .ret (.const (.cap 0)) := rfl
example : (run₂C 80 (closeW F, σW)).1 = .ret (.const (.cap 0)) := rfl
example : (run₂ 80 (closeW F, σW)).2.H.lookup (0 + 1) = some 2 := rfl
example : σW.WF := by decide
example : Placed σW := by intro p n h; simp [σW, mkWorld] at h; omega
example : CellsInR σW := by decide
