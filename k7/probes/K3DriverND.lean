import K7
import S3.Driver3
import S3.DriverN
open Lean Elab Command

/-- Print every constant in a declaration's TYPE, one per line, tagged with the declaration. -/
elab "#k3consts S3.drv_iter_N
#k3consts K7.drv_iter_D
#k3consts K7.deflate_x86_N
-- positive control: a statement ABOUT the router must falsify the whitelist
#k3consts K7.router_served_x86
