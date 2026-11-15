/-
  O95, **K7-b2** (compiler/DECLARATIONS-K7.md, Addenda 2–3): the router's five exits witnessed at the x86 machine. `exit_code` is
  generic in the world: a source run to `ret ⟨0⟩` (`run₂`) and a checked run (`run₂C`) carry, through S1∘S2 (with σ.R kept) and S3,
  to a machine that returns DONE with each cell of the final store at its scaled address. OVF is excluded by `compile_noovf`, RES by
  `resWhy_false` (F's table is empty). The five witnesses are A.4's inputs on L3's world; their facts are evaluation only.
-/
import K7.RouterX86
import K7.World
import K5.Checked
import S3.ResFree

namespace K7
open VIRL1 VIRL2 VIRC VIRL3 K5

/-- The shared S3 premises for the router's lowered code P at base, with layout L. -/
structure Rig (ilen : X86.Op → Nat) (base : W) (C : S3.Ctx3) (P : X86.Program) (L : S3.Lay3) : Prop where
  hCdef : C = S3.ctxOf ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base
  hP : P = S3.lower3 ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base
  hC : ∀ o, 1 ≤ ilen o
  hb : S3.bytes C (S3.allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64
  hN : 5 ≤ L.bufN
  hL : L.Ok
  hcanon : ∀ a i, P.at? a = some i → X86.canonical a = true
  hretc : X86.canonical L.ret0 = true
  hstub : L.stubRet = base + BitVec.ofNat 64 (S3.bytes C (S3.stubHead C))
  hE : 8 * S3.envM (lower2T [tcap] F []).1 2 ≤ L.env0.toNat - L.envLo.toNat
  hS : 16 * (S3.frD (lower2T [tcap] F []).1 + 2) + 8 ≤ L.rsp0.toNat + 8 - L.stkLo.toNat

/-- **exit_code.** For a world σ (W87) on which F's run reaches `ret ⟨0⟩` with final store σ' and whose checked run also reaches it,
    and a machine at base in DriverCall on σ's loader image: the machine returns DONE, and the CODE cell (cell 1) of σ' is at its
    scaled address. -/
theorem exit_code {σ σ' σc : Store} {k kc : Nat} {code : Int} (hW : W87 σ)
    (hrun : run₂ k (closeW F, σ) = (.ret (.const (.cap 0)), σ'))
    (hrunC : run₂C kc (closeW F, σ) = (.ret (.const (.cap 0)), σc))
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
    rw [hinst]; exact srcInRange_of_runC hrunC
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

/-! ## The five witnesses: A.4's inputs on L3's world (sender 0, topic 0), magic bytes 49 71 83 77 at cells 3–6. -/

/-- truncated: LEN 10, ACL bit set, 5 tokens. -/
def wTrunc : Store := mkWorld [(0, 10), (3, 49), (4, 71), (5, 83), (6, 77), (A, 1), (K, 5)]
/-- bad magic: byte 0 is 0. -/
def wMagic : Store := mkWorld [(0, 24), (3, 0), (4, 71), (5, 83), (6, 77), (A, 1), (K, 5)]
/-- ACL bit 0. -/
def wAcl : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (A, 0), (K, 5)]
/-- 0 tokens. -/
def wRate : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (A, 1), (K, 0)]
/-- emit. -/
def wEmit : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (A, 1), (K, 5)]

theorem w87_wTrunc : W87 wTrunc := mkWorld_w87 _ (by simp [inRange])
theorem w87_wMagic : W87 wMagic := mkWorld_w87 _ (by simp [inRange])
theorem w87_wAcl : W87 wAcl := mkWorld_w87 _ (by simp [inRange])
theorem w87_wRate : W87 wRate := mkWorld_w87 _ (by simp [inRange])
theorem w87_wEmit : W87 wEmit := mkWorld_w87 _ (by simp [inRange])

set_option maxRecDepth 100000

theorem run_wTrunc : run₂ 80 (closeW F, wTrunc) = (.ret (.const (.cap 0)), (run₂ 80 (closeW F, wTrunc)).2) := Prod.ext rfl rfl
theorem runC_wTrunc : run₂C 80 (closeW F, wTrunc) = (.ret (.const (.cap 0)), (run₂C 80 (closeW F, wTrunc)).2) := Prod.ext rfl rfl
theorem code_wTrunc : (run₂ 80 (closeW F, wTrunc)).2.H.lookup (0 + 1) = some 1 := rfl
theorem run_wMagic : run₂ 80 (closeW F, wMagic) = (.ret (.const (.cap 0)), (run₂ 80 (closeW F, wMagic)).2) := Prod.ext rfl rfl
theorem runC_wMagic : run₂C 80 (closeW F, wMagic) = (.ret (.const (.cap 0)), (run₂C 80 (closeW F, wMagic)).2) := Prod.ext rfl rfl
theorem code_wMagic : (run₂ 80 (closeW F, wMagic)).2.H.lookup (0 + 1) = some 2 := rfl
theorem run_wAcl : run₂ 80 (closeW F, wAcl) = (.ret (.const (.cap 0)), (run₂ 80 (closeW F, wAcl)).2) := Prod.ext rfl rfl
theorem runC_wAcl : run₂C 80 (closeW F, wAcl) = (.ret (.const (.cap 0)), (run₂C 80 (closeW F, wAcl)).2) := Prod.ext rfl rfl
theorem code_wAcl : (run₂ 80 (closeW F, wAcl)).2.H.lookup (0 + 1) = some 2 := rfl
theorem run_wRate : run₂ 80 (closeW F, wRate) = (.ret (.const (.cap 0)), (run₂ 80 (closeW F, wRate)).2) := Prod.ext rfl rfl
theorem runC_wRate : run₂C 80 (closeW F, wRate) = (.ret (.const (.cap 0)), (run₂C 80 (closeW F, wRate)).2) := Prod.ext rfl rfl
theorem code_wRate : (run₂ 80 (closeW F, wRate)).2.H.lookup (0 + 1) = some 2 := rfl
theorem run_wEmit : run₂ 80 (closeW F, wEmit) = (.ret (.const (.cap 0)), (run₂ 80 (closeW F, wEmit)).2) := Prod.ext rfl rfl
theorem runC_wEmit : run₂C 80 (closeW F, wEmit) = (.ret (.const (.cap 0)), (run₂C 80 (closeW F, wEmit)).2) := Prod.ext rfl rfl
theorem code_wEmit : (run₂ 80 (closeW F, wEmit)).2.H.lookup (0 + 1) = some 0 := rfl

/-- **K7-b2, the five exits witnessed.** For the router's lowered code under the shared premises, each of A.4's five inputs, run by
    the machine from DriverCall on its loader image, returns DONE with its CODE word: truncated 1, bad magic 2, ACL 0 2,
    no tokens 2, emit 0. -/
theorem five_exits {ilen : X86.Op → Nat} {base : W} {C : S3.Ctx3} {P : X86.Program} {L : S3.Lay3} (R : Rig ilen base C P L)
    (hlive : ∀ σ, W87 σ → ∀ a, VIRBridge.Live σ scaleLay a → L.live a) :
    (∀ s, S3.DriverCall L (capWords scaleLay 0 87) (scaleMem wTrunc) s → s.rip = base → ∃ mm,
      S3.Returned L S3.stDone (X86.runP P mm s) ∧ S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 1) ∧
    (∀ s, S3.DriverCall L (capWords scaleLay 0 87) (scaleMem wMagic) s → s.rip = base → ∃ mm,
      S3.Returned L S3.stDone (X86.runP P mm s) ∧ S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 2) ∧
    (∀ s, S3.DriverCall L (capWords scaleLay 0 87) (scaleMem wAcl) s → s.rip = base → ∃ mm,
      S3.Returned L S3.stDone (X86.runP P mm s) ∧ S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 2) ∧
    (∀ s, S3.DriverCall L (capWords scaleLay 0 87) (scaleMem wRate) s → s.rip = base → ∃ mm,
      S3.Returned L S3.stDone (X86.runP P mm s) ∧ S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 2) ∧
    (∀ s, S3.DriverCall L (capWords scaleLay 0 87) (scaleMem wEmit) s → s.rip = base → ∃ mm,
      S3.Returned L S3.stDone (X86.runP P mm s) ∧ S3.rd (X86.runP P mm s).mem (cellAddr (scaleLay 0) (BitVec.ofNat 64 1)) = BitVec.ofInt 64 0) :=
  ⟨fun s hD hrip => exit_code w87_wTrunc run_wTrunc runC_wTrunc code_wTrunc R hD hrip (hlive _ w87_wTrunc),
   fun s hD hrip => exit_code w87_wMagic run_wMagic runC_wMagic code_wMagic R hD hrip (hlive _ w87_wMagic),
   fun s hD hrip => exit_code w87_wAcl run_wAcl runC_wAcl code_wAcl R hD hrip (hlive _ w87_wAcl),
   fun s hD hrip => exit_code w87_wRate run_wRate runC_wRate code_wRate R hD hrip (hlive _ w87_wRate),
   fun s hD hrip => exit_code w87_wEmit run_wEmit runC_wEmit code_wEmit R hD hrip (hlive _ w87_wEmit)⟩

end K7
