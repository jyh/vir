/-
  O95 L5, Lean arm: the LV9 instrument (DECLARATIONS-LEAN Addendum 6, written before this file). One tab-separated `LV9` line per
  row; `count.py --arm lv9` reads them from the logged run and computes every difference itself. Nothing here is a theorem.
-/
import VIRL5
open VIRL1 VIRL2 VIRL3 VIRL5 VIRDeflate.Step

namespace Lv9

/-- A routine's fingerprint: its signature and its body's node count (Addendum 6). -/
abbrev FP := Ty₅ × Nat × Ty₅ × Nat

mutual
/-- Nodes of an atom with routine atoms counted as one; the FPs of the routine atoms met. -/
def nA : Atom₅ → Nat × List FP
  | .var _ => (1, [])
  | .const _ => (1, [])
  | .prim _ as => let r := nL as; (1 + r.1, r.2)
  | .lam _ _ e => let r := nT e; (1 + r.1, r.2)
  | .fix τ₁ k τ₂ e => if 1 ≤ k then (1, [(τ₁, k, τ₂, (nT e).1)]) else let r := nT e; (1 + r.1, r.2)
  | .pair a b => let x := nA a; let y := nA b; (1 + x.1 + y.1, x.2 ++ y.2)
  | .fst a => let r := nA a; (1 + r.1, r.2)
  | .snd a => let r := nA a; (1 + r.1, r.2)
  | .inl _ a => let r := nA a; (1 + r.1, r.2)
  | .inr _ a => let r := nA a; (1 + r.1, r.2)
def nL : List Atom₅ → Nat × List FP
  | [] => (0, [])
  | a :: as => let x := nA a; let y := nL as; (x.1 + y.1, x.2 ++ y.2)
def nT : Tm₅ → Nat × List FP
  | .ret a => let r := nA a; (1 + r.1, r.2)
  | .letE _ e₁ e₂ => let x := nT e₁; let y := nT e₂; (1 + x.1 + y.1, x.2 ++ y.2)
  | .letOp _ as _ e => let x := nL as; let y := nT e; (1 + x.1 + y.1, x.2 ++ y.2)
  | .app a b => let x := nA a; let y := nA b; (1 + x.1 + y.1, x.2 ++ y.2)
  | .ite a e₁ e₂ => let x := nA a; let y := nT e₁; let z := nT e₂; (1 + x.1 + y.1 + z.1, x.2 ++ y.2 ++ z.2)
  | .case a e₁ e₂ => let x := nA a; let y := nT e₁; let z := nT e₂; (1 + x.1 + y.1 + z.1, x.2 ++ y.2 ++ z.2)
  | .retK a ds => let x := nA a; let y := nL ds; (1 + x.1 + y.1, x.2 ++ y.2)
  | .appK a b cs => let x := nA a; let y := nA b; let z := nL cs; (1 + x.1 + y.1 + z.1, x.2 ++ y.2 ++ z.2)
  | .letK _ _ e₁ e₂ => let x := nT e₁; let y := nT e₂; (1 + x.1 + y.1, x.2 ++ y.2)
end

/-- The library's own six, fingerprinted from their definitions (never typed by hand). -/
def fpOf : Atom₅ → Option FP
  | .fix τ₁ k τ₂ e => some (τ₁, k, τ₂, (nT e).1)
  | _ => none

def library : List (String × Atom₅) :=
  [("bitR", bitR), ("copyR", copyR), ("fillR", fillR), ("scanR", scanR), ("cmpR", cmpR), ("copyWithinR", copyWithinR)]

def libFP : List (String × FP) := library.filterMap fun (n, a) => (fpOf a).map (n, ·)

def nameOf (fp : FP) : String := ((libFP.find? fun (_, g) => decide (g = fp)).map Prod.fst).getD "UNKNOWN"

def callsStr (fs : List FP) : String :=
  match fs with
  | [] => "-"
  | _ => ",".intercalate (fs.map nameOf)

def row (prog mode kind : String) (l2 : Tm₅) (l5 : Tm₅) : String :=
  let a := nT l2; let b := nT l5
  s!"LV9\t{prog}\t{mode}\t{kind}\t{a.1}\t{b.1}\t{callsStr b.2}\t{callsStr a.2}"

def modeName (k : Int) : String :=
  match k with
  | 0 => "TABLE" | 1 => "HDR" | 2 => "READ" | 3 => "HDRB" | 4 => "HDRD" | 5 => "SHDR" | 6 => "FIXLENS" | 7 => "DHDR"
  | 8 => "SLEN" | 9 => "SNLEN" | 10 => "SCOPY" | 11 => "BUILD" | 12 => "LENS" | 13 => "SYM" | 14 => "DECODE" | 15 => "SYMD"
  | 16 => "LENX" | 17 => "DSTD" | 18 => "DSTX" | 19 => "COPY" | 20 => "DH2" | 21 => "DH3" | 22 => "DH4" | 23 => "CLREAD"
  | 24 => "CLPUT" | 25 => "LSYM" | 26 => "LREP" | 27 => "REP" | _ => s!"M{k}"

/-- One row per mode of DEFLATE's dispatch, in `modes` order; the L5 side is `modes₅`'s entry for the same number. -/
def deflateRows : List String :=
  modes.map fun (k, m) =>
    match modes₅.lookup k with
    | some t => row "DEFLATE" (modeName k) "mode" (lift₅ m) t
    | none => s!"LV9\tDEFLATE\t{modeName k}\tMISSING\t-\t-\t-\t-"

end Lv9

open Lv9 in
#eval do
  for (n, fp) in libFP do
    IO.println s!"LV9FP\t{n}\t{fp.2.1}\t{fp.2.2.2}"
  for r in deflateRows do IO.println r
  IO.println (row "DEFLATE" "TOTAL" "program" (ιE stepT) stepT₅)
  IO.println (row "ROUTER" "TOTAL" "program" (ιE F) F₅)
