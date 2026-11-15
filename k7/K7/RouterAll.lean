/-
  O95, STATUS-vir 361 (compiler/DECLARATIONS-K7.md, Addendum 4): F's SrcInRange for EVERY world at base 0 (W87) whose wire cells
  hold bytes (inputs/L3-programs.md), so OVF is excluded at the machine for every such world, not only at K7's five witnesses.
  A ROUTER lemma: it is reported beside K7 and is not part of K7's score (Addendum 3). A load outside the region is stuck, and a
  stuck configuration with an in-range head is in range (`srcInRange_stuck`).
-/
import K7.RouterExits
import VIRL3.Sym

namespace K7
open VIRL1 VIRL2 VIRL3 VIRC K5

theorem srcInRange_stuck {c : Config} (hb : headB c.1 = true) (hs : stepFn₂ c.1 c.2 = none) : SrcInRange c := by
  intro S hS
  cases hS with
  | refl => exact headB_sound _ hb
  | step h _ => have := step₂_complete h; rw [hs] at this; cases this

theorem inR_sub1 {x : Int} (h0 : 0 < x) (h : inRange x = true) : inRange (x - 1) = true := by
  simp only [inRange, decide_eq_true_eq] at h ⊢; omega

macro "wsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp (disch := omega) [headB, aInR, aInRL,
  cInR, stepFn₂, stepFn, opStep, Store.load, Store.store, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, Const.toL1,
  L1.Prim.interp, Const.ofL1, Const.toBool, Tm.subst, Atom.subst, Atom.substL, inRange_eq, if_pos, if_neg, A, K, NTp, NW, NS, MAGIC, $hs,*])

macro "ws" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine srcInRange_step ?_ ?_ ?_ <;> [(wsimp [$hs,*]; done); (wsimp [$hs,*]; done); (try wsimp [$hs,*])]))

macro "wstuck" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine srcInRange_stuck ?_ ?_ <;> (wsimp [$hs,*]; done)))

set_option maxHeartbeats 4000000 in
/-- **router_inR, the world form.** F's SrcInRange on an arbitrary world at base 0 whose cells are in range and whose wire cells
    (3 … 66) hold bytes. -/
theorem router_inR_f {σ : Store} {f : Int → Int} (hw : World σ 0 f) (hR : ∀ i, inRange (f i) = true)
    (hwire : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256) : SrcInRange (closeAt 0 F, σ) := by
  have hc : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by
    have := hw.cell i h0 h1; rwa [zero_add] at this
  have hR1 : ∀ i, 0 < f i → inRange (f i - 1) = true := fun i h => inR_sub1 h (hR i)
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
  ws [hreg, hc]
  by_cases hn : 24 ≤ f 0
  · ws [hn]
    repeat ws [hreg, hc]
    by_cases hA : 67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 +
        (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14)))) < 87
    · ws [hreg, hc, hA]
      by_cases hT : 83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) < 87
      · ws [hreg, hc, hT]
        by_cases e1 : f 3 + (256 * f 4 + (65536 * f 5 + 16777216 * f 6)) = 1297303345
        · by_cases e2 : f (67 + ((f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))) * 4 + (f 11 + (256 * f 12 + (65536 * f 13 + 16777216 * f 14))))) = 1
          · by_cases e3 : 0 < f (83 + (f 7 + (256 * f 8 + (65536 * f 9 + 16777216 * f 10))))
            · repeat ws [hreg, hc, hT, e1, e2, e3, hR1]
              exact srcInRange_ret trivial
            · repeat ws [hreg, hc, e1, e2, e3]
              exact srcInRange_ret trivial
          · repeat ws [hreg, hc, e1, e2]
            exact srcInRange_ret trivial
        · repeat ws [hreg, hc, e1]
          exact srcInRange_ret trivial
      · wstuck [hreg, hc, hT]
    · wstuck [hreg, hc, hA]
  · ws [hn]
    repeat ws [hreg, hc]
    exact srcInRange_ret trivial

/-- The wire premise of inputs/L3-programs.md: cells 3 … 3+NW−1 hold bytes. -/
def WireB (σ : Store) : Prop := ∀ i v, 3 ≤ i → i < 67 → σ.H.lookup i = some v → 0 ≤ v ∧ v < 256

/-- **router_inR.** F's SrcInRange for every W87 world with the wire premise. -/
theorem router_inR {σ : Store} (hW : W87 σ) (hwire : WireB σ) : SrcInRange (closeW F, σ) := by
  let f : Int → Int := fun i => (σ.H.lookup i).getD 0
  have hdom : ∀ i, 0 ≤ i → i < 87 → σ.H.lookup i = some (f i) := fun i h0 h1 => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr ((hW.2.1 i).mpr ⟨h0, h1⟩))
    simp [f, hv]
  have hw : World σ 0 f := ⟨hW.R0, fun i h0 h1 => by rw [zero_add]; exact hdom i h0 h1⟩
  have hR : ∀ i, inRange (f i) = true := fun i => by
    cases hl : σ.H.lookup i with
    | none => simp [f, hl, inRange]
    | some v => simpa [f, hl] using hW.2.2 i v hl
  have hb : ∀ i, 3 ≤ i → i < 67 → 0 ≤ f i ∧ f i < 256 := fun i h0 h1 =>
    hwire i (f i) h0 h1 (hdom i (by omega) (by omega))
  exact router_inR_f hw hR hb

/-- **exit_code_all.** `exit_code` with its checked-run premise replaced by the wire premise (DECLARATIONS-K7 Addendum 4): for
    EVERY world σ (W87, wire bytes) on which F's run reaches `ret ⟨0⟩` with final store σ',
    and a machine at base in DriverCall on σ's loader image: the machine returns DONE, and the CODE cell (cell 1) of σ' is at its
    scaled address. -/
theorem exit_code_all {σ σ' : Store} {k : Nat} {code : Int} (hW : W87 σ)
    (hrun : run₂ k (closeW F, σ) = (.ret (.const (.cap 0)), σ'))
    (hwire : WireB σ)
    (hcode : σ'.H.lookup (0 + 1) = some code)
    {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3} (R : Rig ilen base C P L)
    {s : X86.Cpu} (hD : S3.DriverCall L (capWords scaleLay 0 87) (scaleMem σ) s) (hrip : s.rip = base)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a) :
    ∃ mm, S3.Returned L S3.stDone (X86.runP P mm s) ∧
      S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 code := by
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
      refine ⟨mm, hRet, ?_⟩
      have hlv : L.live (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) := hlive _ ⟨0, 87, 1, hW.R0, by decide, rfl⟩
      have hrep := hcm.2.2.2 _ hlv
      simp only [S3.rd]; rw [hrep]
      exact hm' 0 87 (by rw [hR']; exact hW.R0) 1 (by decide) code hcode
    · exfalso
      rw [F_tbl_nil] at hj'
      exact S3.resWhy_false hj' R.hE R.hS hwhy
  · exact absurd hov (compile_noovf [tcap] [true] F tcap [.const (.cap 0)] _ F_typed F_wfB F_fnOk F_ok2 rfl (good_cap 0) F_table
      he hl hm hsrc j W' hWN)

end K7
