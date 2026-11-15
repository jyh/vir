/-
  O95, STATUS-vir 361 part 2 (compiler/DECLARATIONS-K7.md, Addendum 5): R4 carried to the x86 machine as TOTAL correctness on R4's
  own premises (sender < 4, topic < 4), for EVERY W87 world with the wire premise. Termination by a symbolic walk (`router_halts`),
  the post-state from L3's R4 at frame ∅ (`router_post`, l3 unedited), OVF from `router_inR`, RES from `resWhy_false`.
  A ROUTER result, reported beside K7, never inside its score (Addendum 3).
-/
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
    · simp only [hp, if_false]
      have hne : (Finmap.singleton (β := fun _ : Int => Nat) 0 87).lookup p = none :=
        Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hp)
      exact hne.symm
  · by_cases ha : Store.InRegion a 0 87
    · rw [if_pos ha]
      have hm : a ∈ σ.H := (hW.2.1 a).mpr (by simp only [Store.InRegion] at ha; push_cast at ha; omega)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr hm)
      simp [hv]
    · rw [if_neg ha]
      have hm : a ∉ σ.H := fun h => ha (by have := (hW.2.1 a).mp h; simp only [Store.InRegion]; push_cast; omega)
      exact Finmap.lookup_eq_none.mpr hm


/-- σ's cells, as a function (0 outside the heap). -/
def cells (σ : Store) : Int → Int := fun a => (σ.H.lookup a).getD 0

theorem w87_world {σ : Store} (hW : W87 σ) : World σ 0 (cells σ) := by
  refine ⟨hW.R0, fun i h0 h1 => ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr ((hW.2.1 (0 + i)).mpr ⟨by omega, by omega⟩))
  rw [zero_add] at hv ⊢; simp [cells, hv]

theorem wire_cells {σ : Store} (hW : W87 σ) (hwire : WireB σ) : ∀ i, 3 ≤ i → i < 67 → 0 ≤ cells σ i ∧ cells σ i < 256 :=
  fun i h0 h1 => hwire i _ h0 h1 (by have := (w87_world hW).cell i (by omega) (by omega); rwa [zero_add] at this)

/-- **router_halts.** On R4's premises, F's source run reaches `ret ⟨0⟩` for every W87 world with the wire premise. -/
theorem router_halts {σ : Store} (hW : W87 σ) (hwire : WireB σ) (hs4 : SvA (cells σ) 0 < 4) (ht4 : TvA (cells σ) 0 < 4) :
    ∃ k σ', run₂ k (closeW F, σ) = (.ret (.const (.cap 0)), σ') :=
  router_halts_f (w87_world hW) (wire_cells hW hwire) hs4 ht4

/-- **router_post.** The final store of any finishing run is R4's post-state (L3's R4 at frame ∅). -/
theorem router_post {σ σ' : Store} {k : Nat} (hW : W87 σ) (hwire : WireB σ) (hs4 : SvA (cells σ) 0 < 4)
    (ht4 : TvA (cells σ) 0 < 4) (hrun : run₂ k (closeW F, σ) = (.ret (.const (.cap 0)), σ')) :
    RegionAt 0 87 (postF (cells σ) 0) σ' := by
  have hb := wire_cells hW hwire
  have b7 := hb 7 (by decide) (by decide); have b8 := hb 8 (by decide) (by decide)
  have b9 := hb 9 (by decide) (by decide); have b10 := hb 10 (by decide) (by decide)
  have b11 := hb 11 (by decide) (by decide); have b12 := hb 12 (by decide) (by decide)
  have b13 := hb 13 (by decide) (by decide); have b14 := hb 14 (by decide) (by decide)
  have hs0 : 0 ≤ SvA (cells σ) 0 := by simp only [SvA, zero_add]; omega
  have ht0 : 0 ≤ TvA (cells σ) 0 := by simp only [TvA, zero_add]; omega
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  obtain ⟨-, h2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty (w87_regionAt hW) hdisj (by rw [store_empty_union_right]; exact hW.wf)
  have hs : Steps₂ (closeAt 0 F, σ ⊎ Store.empty) (.ret (.const (.cap 0)), σ') := by
    rw [store_empty_union_right]; rw [← hrun]; exact run₂_steps k _
  obtain ⟨v, σq, -, -, hσ', -, -, hq⟩ := h2 _ _ hs
  rw [hσ', store_empty_union_right]; exact hq

theorem exit_cells_all {σ σ' : Store} {k : Nat} (hW : W87 σ)
    (hrun : run₂ k (closeW F, σ) = (.ret (.const (.cap 0)), σ'))
    (hwire : WireB σ)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3} (R : Rig ilen base C P L)
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay 0 87) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a) :
    ∃ mm, S3.Returned L S3.stDone (X86.runP P mm s) ∧
      ∀ i : Nat, i < 87 → ∀ v, σ'.H.lookup (0 + (i : Int)) = some v →
        S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 i)) = BitVec.ofInt 64 v := by
  have hinst : instL 0 [(Atom.const (.cap 0) : Atom₂)] F = closeW F := rfl
  have hs : Steps₂ (instL 0 [(Atom.const (.cap 0) : Atom₂)] F, σ) (.ret (.const (.cap 0)), σ') := by
    rw [hinst, ← hrun]; exact run₂_steps k _
  have hsrc : SrcInRange (instL 0 [(Atom.const (.cap 0) : Atom₂)] F, σ) := by
    rw [hinst]; exact router_inR hW hwire
  obtain ⟨hl, hm⟩ := loader_ok hW.wf hW.placed hW.cellsInR
  have he := envRel_cap1 (T := (lower2T [tcap] F []).2) (lay := scaleLay) hW.R0
  rcases S3.compile_refines_mem_R [tcap] [true] F tcap [.const (.cap 0)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap 0) F_table
      he hl hm _ σ' _ hs rfl with ⟨j, ws, m', hWN, hv, hl', hm', hR'⟩ | ⟨j, W', hWN, hov⟩
  · have h0 := s2_init [tcap] [true] F tcap _ _ F_typed F_wfB F_fnOk F_ok2 he hl hm
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j', hj', -, hwhy, -, -⟩⟩ :=
      S3.s3_refines_from_s2 R.hCdef R.hP R.hC R.hb F_table (le_trans F_need R.hN)
        (by rw [F_tbl_nil]; intro x hx; cases hx) R.hL R.hcanon R.hretc R.hstub hD hrip h0 hlive hWN
    · obtain ⟨hRet, hcm, -, -⟩ := hR3
      refine ⟨mm, hRet, fun i hi v hv => ?_⟩
      have hlv : L.live (cellAddr (scaleLay 0) (BitVec.ofNat 64 i)) := hlive _ ⟨0, 87, i, hW.R0, hi, rfl⟩
      have hrep := hcm.2.2.2 _ hlv
      simp only [S3.rd]; rw [hrep]
      exact hm' 0 87 (by rw [hR']; exact hW.R0) i hi v hv
    · exfalso
      rw [F_tbl_nil] at hj'
      exact S3.resWhy_false hj' R.hE R.hS hwhy
  · exact absurd hov (compile_noovf [tcap] [true] F tcap [.const (.cap 0)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap 0) F_table
      he hl hm hsrc j W' hWN)


/-- **router_R4_x86.** R4 at the x86 machine as TOTAL correctness on R4's own premises, for EVERY W87 world with the wire premise:
    the machine returns DONE and every one of the world's 87 cells is at its scaled address with R4's post-state value. -/
theorem router_R4_x86 {σ : Store} (hW : W87 σ) (hwire : WireB σ) (hs4 : SvA (cells σ) 0 < 4) (ht4 : TvA (cells σ) 0 < 4)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3} (R : Rig ilen base C P L)
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay 0 87) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a) :
    ∃ mm, S3.Returned L S3.stDone (X86.runP P mm s) ∧
      ∀ i : Nat, i < 87 →
        S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 i)) = BitVec.ofInt 64 (postF (cells σ) 0 i) := by
  obtain ⟨k, σ', hrun⟩ := router_halts hW hwire hs4 ht4
  have hpost := router_post hW hwire hs4 ht4 hrun
  obtain ⟨mm, hRet, hall⟩ := exit_cells_all hW hrun hwire R hD hrip hlive
  refine ⟨mm, hRet, fun i hi => hall i hi _ ?_⟩
  rw [hpost.2, if_pos (by simp only [Store.InRegion]; omega), zero_add]

end K7
