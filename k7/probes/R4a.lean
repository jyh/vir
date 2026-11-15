import K7.RouterAll
import VIRL3.RouterTriple
import VIRL2.Triples
open VIRL1 VIRL2 VIRL3 VIRC K5

namespace K7

def Halts (c : Config) : Prop := ∃ k σ', run₂ k c = (.ret (.const (.cap 0)), σ')

theorem halts_ret (σ : Store) : Halts (.ret (.const (.cap 0)), σ) := ⟨0, σ, rfl⟩

theorem halts_step {c : Config} (hs : (stepFn₂ c.1 c.2).isSome = true) (h : Halts ((stepFn₂ c.1 c.2).getD c)) : Halts c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
  rw [hc'] at h
  obtain ⟨k, σ', hk⟩ := h
  exact ⟨k + 1, σ', by simp only [run₂, hc']; exact hk⟩

macro "hs" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine halts_step ?_ ?_ <;> [(wsimp [$hs,*]; done); (try wsimp [$hs,*])]))

set_option maxHeartbeats 4000000 in
theorem router_halts_f {σ : Store} {f : Int → Int} (hw : World σ 0 f)
    (hwire : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256) (hs4 : SvA f 0 < 4) (ht4 : TvA f 0 < 4) :
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

/-- A W87 world is L2's RegionAt 0 87 of its own cells. -/
theorem w87_regionAt {σ : Store} (hW : W87 σ) : RegionAt 0 87 (fun a => (σ.H.lookup a).getD 0) σ := by
  refine ⟨?_, fun a => ?_⟩
  · apply Finmap.ext_lookup; intro p
    rw [hW.1 p]; by_cases hp : p = 0
    · subst hp; simp
    · simp [hp, Finmap.lookup_singleton_eq]
  · by_cases ha : Store.InRegion a 0 87
    · rw [if_pos ha]
      have hm : a ∈ σ.H := (hW.2.1 a).mpr (by simp only [Store.InRegion] at ha; push_cast at ha; omega)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr hm)
      simp [hv]
    · rw [if_neg ha]
      have hm : a ∉ σ.H := fun h => ha (by have := (hW.2.1 a).mp h; simp only [Store.InRegion]; push_cast; omega)
      exact Finmap.lookup_eq_none.mpr hm

end K7
