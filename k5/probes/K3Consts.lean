import K5.DeflateNoOvf
open Lean Elab Command

/-- Print every constant in a declaration's TYPE, one per line, tagged with the declaration. -/
elab "#k3consts " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  match env.find? n with
  | none => logError m!"no such constant {n}"
  | some ci =>
    for c in ci.type.getUsedConstants do
      logInfo m!"K3CONST {n} {c}"

#k3consts VIRC.compile_refines
#k3consts VIRC.compile_noovf
#k3consts VIRC.compile_refines_noovf
#k3consts VIRC.s2_refines
-- positive control: a statement ABOUT DEFLATE must falsify the whitelist
#k3consts K5.deflate_noovf
