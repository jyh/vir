import K7.DeflateX86N
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5 S3

-- row 373 measurement: DEFLATE's lowered step — table size, and whether any call is NON-tail (an `app` inside a letE's first arm).
def hasApp : WCode → Bool
  | .ret _ => false
  | .letE c₁ c₂ => hasApp c₁ || hasApp c₂
  | .load _ _ k => hasApp k
  | .store _ _ _ k => hasApp k
  | .app _ _ => true
  | .ite _ c₁ c₂ => hasApp c₁ || hasApp c₂
  | .case _ _ _ c₁ c₂ => hasApp c₁ || hasApp c₂

def appUnderLet : WCode → Bool
  | .ret _ => false
  | .letE c₁ c₂ => hasApp c₁ || appUnderLet c₁ || appUnderLet c₂
  | .load _ _ k => appUnderLet k
  | .store _ _ _ k => appUnderLet k
  | .app _ _ => false
  | .ite _ c₁ c₂ => appUnderLet c₁ || appUnderLet c₂
  | .case _ _ _ c₁ c₂ => appUnderLet c₁ || appUnderLet c₂

#eval (lower2T [tcap] stepT []).2.length
#eval ((lower2T [tcap] stepT []).2.map (fun x => appUnderLet x.2))
#eval appUnderLet (lower2T [tcap] stepT []).1
#eval hasApp (lower2T [tcap] stepT []).1
#eval (envM (lower2T [tcap] stepT []).1 2, frD (lower2T [tcap] stepT []).1)
#eval ((lower2T [tcap] stepT []).2.map (fun x => (envM x.2 3, frD x.2)))
