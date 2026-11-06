/-
  O95 layer L3, Lean arm. The transcription check's Lean half (l3/DECLARATIONS-LEAN.md): F, U and U_tx printed as
  S-expressions over L2's de Bruijn syntax. `harness/transcribe_l3.py` builds the same S-expressions from the TEXT of
  inputs/L3-programs.md (its own parser, its own macro expansion, its own name → index compiler) and compares.
-/
import VIRL3.Router

namespace VIRL3
open VIRL1 VIRL2

def sPrim : L1.Prim → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .lt => "lt" | .le => "le" | .eq => "eq" | .and => "and"
  | .or => "or" | .not => "not" | .max => "max"
def sOp : Op → String
  | .alloc => "alloc" | .load => "load" | .store => "store" | .free => "free"
def sTy : Ty₂ → String
  | .base .int => "int" | .base .cap => "cap" | .base .bool => "bool" | .base .unit => "unit" | _ => "?"

mutual
def sA : Atom₂ → String
  | .var n => s!"#{n}"
  | .const (.int n) => toString n
  | .const (.cap p) => s!"cap{p}"
  | .const _ => "?"
  | .prim p as => s!"({sPrim p}{sAL as})"
  | _ => "?"
def sAL : List Atom₂ → String
  | [] => ""
  | a :: as => " " ++ sA a ++ sAL as
end

def sT : Tm₂ → String
  | .ret a => s!"(ret {sA a})"
  | .letE τ e₁ e₂ => s!"(let {sTy τ} {sT e₁} {sT e₂})"
  | .letOp o as τ e => s!"({sOp o} {sTy τ} [{(sAL as).drop 1}] {sT e})"
  | .ite a e₁ e₂ => s!"(if {sA a} {sT e₁} {sT e₂})"
  | _ => "?"

#eval IO.println ("F " ++ sT F)
#eval IO.println ("U " ++ sT U)
#eval IO.println ("U_tx " ++ sT U_tx)

end VIRL3
