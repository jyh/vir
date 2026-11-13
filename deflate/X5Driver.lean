/-
X5Driver.lean — the ARM's side of the X5 run (DECLARATIONS-DEFLATE.md, Addendum A2). HARNESS, not the arm: outside lib
`VIRDeflate`, so it is in neither of D5's file groups.
usage: x5 OUTDIR IN…   -> for each IN, runs `inflateLit` and `inflate` with OUTMAX = 2^26, writes OUTDIR/<base>.lit.bin and
OUTDIR/<base>.rep.bin for an ACCEPT, and prints one line per input:  <base> \t <lit verdict> \t <rep verdict>
where a verdict is `ACCEPT <nbytes>` or `REJECT <reason>`.
-/
import VIRDeflate.Spec

open VIRDeflate

def outmax : Nat := 2 ^ 26

def verdictLine (r : Except String (Array Nat)) : String :=
  match r with
  | .ok o => s!"ACCEPT {o.size}"
  | .error e => s!"REJECT {e}"

def toBytes (a : Array Nat) : ByteArray := ⟨a.map (fun x => UInt8.ofNat x)⟩

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: x5 OUTDIR IN…"; return 2
  | outdir :: ins =>
    for p in ins do
      let bytes ← IO.FS.readBinFile p
      let b : Array Nat := bytes.data.map (·.toNat)
      let base := ((System.FilePath.mk p).fileStem.getD p)
      let lit := inflateLit b outmax
      let rep := inflate b outmax
      if let .ok o := lit then IO.FS.writeBinFile (System.FilePath.mk outdir / s!"{base}.lit.bin") (toBytes o)
      if let .ok o := rep then IO.FS.writeBinFile (System.FilePath.mk outdir / s!"{base}.rep.bin") (toBytes o)
      IO.println s!"{base}\t{verdictLine lit}\t{verdictLine rep}"
    return 0
