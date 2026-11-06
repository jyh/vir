/-
  O95 layer L3, Lean arm. The terms F (A.3's fused term), U (virp's I3) and U_tx (R3), transcribed from inputs/L3-programs.md
  operation for operation, with the world `w` the one free variable (Γ = [w], de Bruijn #0 at the top).
-/
import VIRL3.Layout

namespace VIRL3
open VIRL1 VIRL2

/-- F (inputs/L3-programs.md "F"), named. -/
def Fn : NT :=
  .op "n" tint .load [.v "w", .i 0] <|
  .ite (le (.i 24) (.v "n"))
    (RD32 "w" 0 "magic" <| RD32 "w" 4 "sender" <| RD32 "w" 8 "topic" <|
      .op "a" tint .load [.v "w", add (.i A) (add (mul (.v "sender") (.i NTp)) (.v "topic"))] <|
      .op "t" tint .load [.v "w", add (.i K) (.v "sender")] <|
      .ite (conj (eq (.v "magic") (.i MAGIC)) (conj (eq (.v "a") (.i 1)) (lt (.i 0) (.v "t"))))
        (.op "w1" tcap .store [.v "w", add (.i K) (.v "sender"), sub (.v "t") (.i 1)] (EMIT "w1"))
        (EXIT "w" 2))
    (EXIT "w" 1)

/-- U (inputs/L3-programs.md "U"), named; `rb` is the refusing exit after the decrement (R3 replaces it). -/
def Ugen (rb : NT) : NT :=
  .op "n" tint .load [.v "w", .i 0] <|
  .ite (le (.i 24) (.v "n"))
    (RD32 "w" 0 "magic" <|
      .ite (eq (.v "magic") (.i MAGIC))
        (RD32 "w" 4 "sender" <| RD32 "w" 8 "topic" <|
          .op "t" tint .load [.v "w", add (.i K) (.v "sender")] <|
          .ite (lt (.i 0) (.v "t"))
            (.op "w1" tcap .store [.v "w", add (.i K) (.v "sender"), sub (.v "t") (.i 1)] <|
              .op "a" tint .load [.v "w1", add (.i A) (add (mul (.v "sender") (.i NTp)) (.v "topic"))] <|
              .ite (eq (.v "a") (.i 1)) (EMIT "w1") rb)
            (EXIT "w" 2))
        (EXIT "w" 2))
    (EXIT "w" 1)

def Un : NT := Ugen (EXIT "w1" 2)

/-- U_tx (R3): the post-decrement `EXIT(2)` preceded by `store(w1, add(K, sender), t)`, the decrement undone. -/
def Utxn : NT := Ugen (.op "w2" tcap .store [.v "w1", add (.i K) (.v "sender"), .v "t"] (EXIT "w2" 2))

def F : Tm₂ := Fn.c ["w"]
def U : Tm₂ := Un.c ["w"]
def U_tx : Tm₂ := Utxn.c ["w"]

end VIRL3
