/-
  O95 L5, Lean arm: the LV10 instrument (DECLARATIONS-LEAN Addendum 10, written before this file). Each routine's shape (int
  constants erased) and one tab-separated `LV10` line per unordered pair: equal 1 / 0. `count.py --arm lv10` reads them.
-/
import VIRL5
open VIRL1 VIRL2 VIRL5

namespace Lv10

def cS : Const → String
  | .int _ => "_"
  | c => reprStr c

mutual
def sA : Atom₅ → String
  | .var n => s!"v{n}"
  | .const c => s!"c({cS c})"
  | .prim p as => s!"prim({reprStr p};{sL as})"
  | .lam τ k e => s!"lam({reprStr τ};{k};{sT e})"
  | .fix τ₁ k τ₂ e => s!"fix({reprStr τ₁};{k};{reprStr τ₂};{sT e})"
  | .pair a b => s!"pair({sA a};{sA b})"
  | .fst a => s!"fst({sA a})"
  | .snd a => s!"snd({sA a})"
  | .inl τ a => s!"inl({reprStr τ};{sA a})"
  | .inr τ a => s!"inr({reprStr τ};{sA a})"
def sL : List Atom₅ → String
  | [] => ""
  | a :: as => s!"{sA a},{sL as}"
def sT : Tm₅ → String
  | .ret a => s!"ret({sA a})"
  | .letE τ e₁ e₂ => s!"let({reprStr τ};{sT e₁};{sT e₂})"
  | .letOp o as τ e => s!"op({reprStr o};{sL as};{reprStr τ};{sT e})"
  | .app a b => s!"app({sA a};{sA b})"
  | .ite a e₁ e₂ => s!"ite({sA a};{sT e₁};{sT e₂})"
  | .case a e₁ e₂ => s!"case({sA a};{sT e₁};{sT e₂})"
  | .retK a ds => s!"retK({sA a};{sL ds})"
  | .appK a b cs => s!"appK({sA a};{sA b};{sL cs})"
  | .letK τ j e₁ e₂ => s!"letK({reprStr τ};{j};{sT e₁};{sT e₂})"
end

def library : List (String × Atom₅) :=
  [("bitR", bitR), ("copyR", copyR), ("fillR", fillR), ("scanR", scanR), ("cmpR", cmpR), ("copyWithinR", copyWithinR)]

def pairsOf : List (String × Atom₅) → List String
  | [] => []
  | (a, x) :: rest =>
      rest.map (fun (b, y) => s!"LV10\t{a}\t{b}\t{if sA x == sA y then 1 else 0}\t{(sA x).length}\t{(sA y).length}") ++ pairsOf rest

def pairs : List String := pairsOf library

end Lv10

open Lv10 in
#eval do
  for r in pairs do IO.println r
