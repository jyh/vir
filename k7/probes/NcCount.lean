import K7.RouterX86
import S3.Proved
/- OBJECT-NOCHECK amend-26 NC2's instrument: on the router F, the checked and unchecked lowerings' instruction lists (allCode, the
   lists `lower3B` assembles), counted in total and by the four check classes; and F's load/store sites. -/
open VIRL1 VIRL2 VIRC VIRL3 K5 K7 S3

def sites : WCode → Nat
  | .ret _ => 0
  | .letE c₁ c₂ => sites c₁ + sites c₂
  | .load _ _ k => 1 + sites k
  | .store _ _ _ k => 1 + sites k
  | .app _ _ => 0
  | .ite _ c₁ c₂ => sites c₁ + sites c₂
  | .case _ _ _ c₁ c₂ => sites c₁ + sites c₂

def cls : AI → Nat
  | .op (.bin .test _ _ _) => 1
  | .jccA .s _ => 2
  | .op (.bin .cmp _ _ _) => 3
  | .jccA .ge _ => 4
  | _ => 0

def tally (l : List AI) : List Nat := [l.length] ++ [1, 2, 3, 4].map fun k => (l.filter fun i => cls i == k).length

def nc2 : List Nat × List Nat × Nat :=
  let T := lower2T [tcap] F []
  let Cc := ctxOfB true (fun _ => 1) T.2 T.1 0
  let Cu := ctxOfB false (fun _ => 1) T.2 T.1 0
  (tally (allCode Cc T.2 T.1), tally (allCode Cu T.2 T.1), sites T.1 + (T.2.map fun e => sites e.2).sum)

#eval nc2
