import K7.RouterR4
open VIRL1 VIRL2 VIRL3 VIRC K5
namespace K7
-- GOING RED (DECLARATIONS-K7 Addendum 5): router_halts_f's walk with R4's sender bound widened to < 5 (sender 4's bucket load at
-- 83 + 4 = 87 leaves the region) must fail to close.
set_option maxHeartbeats 4000000 in
example {σ : Store} {f : Int → Int} (hw : World σ 0 f)
    (hwire : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256) (hs4 : SvA f 0 < 5) (ht4 : TvA f 0 < 4) :
    Halts (closeAt 0 F, σ) := by
  simp only [SvA, TvA, zero_add] at hs4 ht4
  have hc : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by
    have := hw.cell i h0 h1; rwa [zero_add] at this
  have h3 := hwire 3 (by decide) (by decide); have h4 := hwire 4 (by decide) (by decide)
  have h5 := hwire 5 (by decide) (by decide); have h6 := hwire 6 (by decide) (by decide)
  have h7 := hwire 7 (by decide) (by decide); have h8 := hwire 8 (by decide) (by decide)
  have h9 := hwire 9 (by decide) (by decide); have h10 := hwire 10 (by decide) (by decide)
  have h11 := hwire 11 (by decide) (by decide); have h12 := hwire 12 (by decide) (by decide)
  have h13 := hwire 13 (by decide) (by decide); have h14 := hwire 14 (by decide) (by decide)
  have hreg := hw.reg
  simp only [closeAt, F, Fn, RD32, EXIT, EMIT, NT.c, NA.c, add, sub, mul, le, lt, eq, conj, List.map, List.idxOf,
    List.findIdx, List.findIdx.go, String.reduceAppend, String.reduceBEq, cond_true, cond_false, Nat.reduceAdd, Nat.zero_add,
    Tm.subst, Atom.subst, Atom.substL, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  hs [hreg, hc]
  by_cases hn : 24 ≤ f 0
  · hs [hn]
    repeat hs [hreg, hc]
    by_cases e1 : f 3 + (256 * f 4 + (65536 * f 5 + 16777216 * f 6)) = 1297303345
    · by_cases e2 : f (67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 +
          (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14))))) = 1
      · by_cases e3 : 0 < f (83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))))
        · repeat hs [hreg, hc, e1, e2, e3]
          exact halts_ret _
        · repeat hs [hreg, hc, e1, e2, e3]
          exact halts_ret _
      · repeat hs [hreg, hc, e1, e2]
        exact halts_ret _
    · repeat hs [hreg, hc, e1]
      exact halts_ret _
  · hs [hn]
    repeat hs [hreg, hc]
    exact halts_ret _

end K7
