/-
  O95 amend-16 Y3 instrument (STATUS-vir row 105), built in the L2 project at its birth, never in l1/ (a build there would move
  L1.C6). `#closure T` prints the TRANSITIVE constants of T (its type and its value, followed through every constant they
  mention) and how many of them are the ⊢₂ family (`VIRL2.HasType₂`, `VIRL2.HasTypeA₂`, `VIRL2.HasTypeL₂` and their
  recursors, constructors and auxiliaries: every name under those three prefixes). The harness reads the printed lines.
  POSITIVE CONTROL: `VIRL2.M1_typed` IS a ⊢₂ judgement, so its line must print typing2 > 0, or the instrument cannot see.
-/
import VIRL2
open Lean Elab Command

def typing2Roots : List Name := [`VIRL2.HasType₂, `VIRL2.HasTypeA₂, `VIRL2.HasTypeL₂]

partial def collectConsts (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then collectConsts env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => collectConsts env rest seen
      | some ci =>
        -- ⛔ `ci.value?` is `none` for a THEOREM (it skips proofs), so a closure built on it follows statements only and reads
        -- 0 for every proof. Found on this instrument's first run, by its own positive control printing 1 where a ⊢₂ proof
        -- uses several constructors (logs/scratch-001.log). Theorem values are read explicitly.
        let val : Option Expr := match ci with
          | .thmInfo t => some t.value
          | .defnInfo d => some d.value
          | .opaqueInfo o => some o.value
          | _ => none
        let cs := ci.type.getUsedConstants.toList ++ (val.map (·.getUsedConstants.toList)).getD []
        collectConsts env (cs ++ rest) seen

elab "#closure " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let all := collectConsts env [n] {}
  let names := all.toList
  let t2 := names.filter fun m => typing2Roots.any fun r => r.isPrefixOf m
  let vir := names.filter fun m => (`VIRL2).isPrefixOf m
  logInfo m!"closure {n}: constants {names.length} · VIRL2 {vir.length} · typing2 {t2.length}"

/-- CONTROL FOR THE PROOF HALF: its STATEMENT is `True`, and its PROOF uses a ⊢₂ derivation. It reads typing2 > 0 only if the
  closure follows proofs; the `value?` version of this file read it 0 (re-driven as mutant-001). -/
theorem control_proof_uses_typing : True := (fun _ => trivial) VIRL2.M1_typed

#closure control_proof_uses_typing
#closure VIRL2.frame
#closure VIRL2.op_frame
#closure VIRL2.M2_triple
#closure VIRL2.M1_typed
