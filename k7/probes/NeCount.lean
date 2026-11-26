import K7.RouterEntry
/- OBJECT-NOCHECK-ENTRY amend-27, the "directions only" row: dF's checked lowering's instruction count (allCode, as NC2's
   instrument counts F), beside F's checked 731 / unchecked 651 (RESULTS-15 NC2); and dF's load sites. -/
open VIRL1 VIRL2 VIRC VIRL3 K5 K7 S3

def sitesD : WCode → Nat
  | .ret _ => 0
  | .letE c₁ c₂ => sitesD c₁ + sitesD c₂
  | .load _ _ k => 1 + sitesD k
  | .store _ _ _ k => 1 + sitesD k
  | .app _ _ => 0
  | .ite _ c₁ c₂ => sitesD c₁ + sitesD c₂
  | .case _ _ _ c₁ c₂ => sitesD c₁ + sitesD c₂

def ne_dir : Nat × Nat × Nat × Nat :=
  let T := lower2T [tcap] dF []
  let Cc := ctxOfB true (fun _ => 1) T.2 T.1 0
  let Cu := ctxOfB false (fun _ => 1) T.2 T.1 0
  ((allCode Cc T.2 T.1).length, (allCode Cu T.2 T.1).length, sitesD T.1 + (T.2.map fun e => sitesD e.2).sum, T.2.length)

#eval ne_dir
