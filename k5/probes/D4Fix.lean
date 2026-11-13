import K5.DeflateNoOvf
open VIRL1 VIRL2 VIRDeflate VIRDeflate.Step
-- D4's instrument: the step program's term. Count `fix` nodes and `prim` operators used in stepT.
mutual
partial def cntA : Atom₂ → Nat × List String
  | .fix _ _ e => let (n, ps) := cntT e; (n + 1, ps)
  | .lam _ e => cntT e
  | .prim p as => as.foldl (fun (n, ps) a => let (m, qs) := cntA a; (n + m, ps ++ qs)) (0, [toString (repr p)])
  | .pair a b => let (n, p) := cntA a; let (m, q) := cntA b; (n + m, p ++ q)
  | .fst a | .snd a | .inl _ a | .inr _ a => cntA a
  | _ => (0, [])
partial def cntT : Tm₂ → Nat × List String
  | .ret a => cntA a
  | .letE _ e₁ e₂ => let (n, p) := cntT e₁; let (m, q) := cntT e₂; (n + m, p ++ q)
  | .letOp _ as _ e => as.foldl (fun (n, ps) a => let (m, qs) := cntA a; (n + m, ps ++ qs)) (cntT e)
  | .app a b => let (n, p) := cntA a; let (m, q) := cntA b; (n + m, p ++ q)
  | .ite a e₁ e₂ | .case a e₁ e₂ => let (n, p) := cntA a; let (m, q) := cntT e₁; let (k, r) := cntT e₂; (n + m + k, p ++ q ++ r)
end
#eval let (n, ps) := cntT stepT; (n, ps.eraseDups)
-- control: a term with exactly one fix must read 1
#eval (cntT (.ret (.fix tint tint (.ret (.var 0))))).1
