import K7
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

#k3consts VIRC.compile_refines_mem
#k3consts VIRC.driver_l2
-- positive control: a statement ABOUT DEFLATE must falsify the whitelist
#k3consts K7.router_refines
