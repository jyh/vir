import K7
import S3.Driver3
import S3.DriverN
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

#k3consts S3.drv_iter_N
#k3consts K7.drv_iter_D
#k3consts K7.deflate_x86_N
-- positive control: a statement ABOUT the router must falsify the whitelist
#k3consts K7.router_served_x86
