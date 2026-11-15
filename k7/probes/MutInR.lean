import K7.RouterAll
open VIRL1 VIRL2 VIRL3 VIRC K5
namespace K7
-- GOING RED (DECLARATIONS-K7 Addendum 4): router_inR_f's proof with the wire premise DROPPED must fail to close.
set_option maxHeartbeats 4000000 in
example {σ : Store} {f : Int → Int} (hw : World σ 0 f) (hR : ∀ i, inRange (f i) = true) :
    SrcInRange (closeAt 0 F, σ) := by
  have hc : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by
    have := hw.cell i h0 h1; rwa [zero_add] at this
  have hreg := hw.reg
  simp only [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  ws [hreg, hc]
  by_cases hn : 24 ≤ f 0
  · ws [hn]
    ws [hreg, hc]; ws [hreg, hc]; ws [hreg, hc]; ws [hreg, hc]; ws [hreg, hc]
  · ws [hn]
    repeat ws [hreg, hc]
    exact srcInRange_ret trivial
end K7
