/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addenda 1–3): the relation between S2's word states and x86lean's `Cpu`.
  The regions are S3-M's: ENV (ρ's words, newest at the LOWEST address, `envLow` in r12), the x86 STACK (per pending `letE`: the
  return address, then the saved `envLow`), BUF (operands and results, base in r14) and CB (control block, base in rbx). S2's word
  memory is related on the live L2 cells by bridge `Rep`. Nothing here is a premise on stored VALUES: the layout facts (`Lay3.Ok`)
  are about placement, and every other conjunct is an invariant the simulation re-establishes.
-/
import S3.Lower3
import VIRBridge.Mem

namespace S3
open VIRC X86

/-- S3-M's placement: the four regions, the driver's frame and the live L2 cells. -/
structure Lay3 where
  envLo : W
  envTop : W
  stkLo : W
  /-- The driver's `rsp` at the entry stub: `[rsp0]` holds the driver's return address `ret0`. -/
  rsp0 : W
  ret0 : W
  buf : W
  bufN : Nat
  cb : W
  /-- The entry stub's return point (the `pop r12` after its call): the top-level continuation. -/
  stubRet : W
  live : W → Prop

def inEnv (L : Lay3) (a : W) : Prop := L.envLo.toNat ≤ a.toNat ∧ a.toNat < L.envTop.toNat
def inStk (L : Lay3) (a : W) : Prop := L.stkLo.toNat ≤ a.toNat ∧ a.toNat < L.rsp0.toNat + 8
def inBuf (L : Lay3) (a : W) : Prop := Region L.buf (8 * L.bufN) a
def inCb (L : Lay3) (a : W) : Prop := Region L.cb 32 a
def inLive (L : Lay3) (a : W) : Prop := ∃ c, L.live c ∧ Region c 8 a

/-- The layout premise (S3-M): ENV and STACK do not wrap, and the five byte sets are pairwise disjoint. -/
structure Lay3.Ok (L : Lay3) : Prop where
  env_nowrap : L.envLo.toNat ≤ L.envTop.toNat
  stk_nowrap : L.rsp0.toNat + 16 < 2 ^ 64
  buf_nowrap : L.buf.toNat + 8 * L.bufN < 2 ^ 64
  cb_nowrap : L.cb.toNat + 32 < 2 ^ 64
  env_stk : ∀ a, inEnv L a → ¬ inStk L a
  env_buf : ∀ a, inEnv L a → ¬ inBuf L a
  env_cb : ∀ a, inEnv L a → ¬ inCb L a
  env_live : ∀ a, inEnv L a → ¬ inLive L a
  stk_buf : ∀ a, inStk L a → ¬ inBuf L a
  stk_cb : ∀ a, inStk L a → ¬ inCb L a
  stk_live : ∀ a, inStk L a → ¬ inLive L a
  buf_cb : ∀ a, inBuf L a → ¬ inCb L a
  buf_live : ∀ a, inBuf L a → ¬ inLive L a
  cb_live : ∀ a, inCb L a → ¬ inLive L a
  live_sep : VIRBridge.Sep L.live

/-- A word list at `a`, word j at `a + 8j` (ρ in ENV, newest first; a result in BUF). -/
def WordsAt (m : Mem) (a : W) (ws : List W) : Prop :=
  ∀ j (h : j < ws.length), m.readN (a + BitVec.ofNat 64 (8 * j)) 8 = ws[j]

def rd (m : Mem) (a : W) : W := m.readN a 8

/-- The code a frame's return address points at: `pop r12`, the runtime prepend, then the continuation's code (gen's `letE`
    layout from the `pop` on). -/
def contCode (C : Ctx3) (q : W) (c₂ : WCode) : List AI :=
  let post := [AI.op (.pop .q (.reg .r12))] ++ prependLoop C (q + BitVec.ofNat 64 (bytes C [AI.op (.pop .q (.reg .r12))]))
  post ++ gen C (q + BitVec.ofNat 64 (bytes C post)) c₂

/-- The top-level continuation, from the entry stub's return point: DONE. -/
def stubCont : List AI := [.op (.pop .q (.reg .r12)), movi .rax stDone, st .rbx 0 .rax, .op .ret]

/-- gen's `letE` is the call prologue, the call, the continuation's code, then c₁'s code (`rfl`: the layout is what Rel3 reads). -/
theorem gen_letE (C : Ctx3) (pc : W) (c₁ c₂ : WCode) :
    gen C pc (.letE c₁ c₂) =
      let pre := stackRoom C ++ [.op (.push .q (.reg .r12))]
      let pAfter := pc + BitVec.ofNat 64 (bytes C pre + 5)
      let p₂ := pAfter + BitVec.ofNat 64 (bytes C ([.op (.pop .q (.reg .r12))] ++
        prependLoop C (pAfter + BitVec.ofNat 64 (bytes C [.op (.pop .q (.reg .r12))]))))
      let p₁ := p₂ + BitVec.ofNat 64 (bytes C (gen C p₂ c₂))
      pre ++ [.callA p₁] ++ contCode C pAfter c₂ ++ gen C p₁ c₁ := by
  simp only [gen, contCode, List.append_assoc]

/-- **Frames** from `rsp`: each pending continuation's return address and saved `envLow`, its code in place, its ρ in ENV at the
    saved `envLow`, and that `envLow` at or above `lo` (the current activation writes only below its base, so nothing pending is
    overwritten). The bottom frame is the entry stub's: its return point, the entry `envLow`, and the driver's slot above it. -/
def Frames (C : Ctx3) (p : Program) (L : Lay3) (m : Mem) : W → W → List (WCode × List W) → Prop
  | rsp, lo, [] => rd m rsp = L.stubRet ∧ CodeAt C p L.stubRet stubCont ∧ lo.toNat ≤ (rd m (rsp + 8)).toNat ∧
      rsp.toNat + 16 = L.rsp0.toNat ∧ rd m L.rsp0 = L.ret0
  | rsp, lo, (c, ρ) :: k => ∃ q a, rd m rsp = q ∧ rd m (rsp + 8) = a ∧ CodeAt C p q (contCode C q c) ∧
      lo.toNat ≤ a.toNat ∧ a.toNat + 8 * ρ.length ≤ L.envTop.toNat ∧ WordsAt m a ρ ∧
      rsp.toNat + 16 ≤ L.rsp0.toNat ∧ Frames C p L m (rsp + 16) a k

/-- The control block (S3-M): `[cb+8]` the driver's `rsp`, `[cb+16]` ENV's low bound, `[cb+24]` STACK's. -/
def CbOk (L : Lay3) (m : Mem) : Prop :=
  rd m (L.cb + 8) = L.rsp0 ∧ rd m (L.cb + 16) = L.envLo ∧ rd m (L.cb + 24) = L.stkLo

/-- The registers and memory every state shares. -/
def Common (L : Lay3) (wm : WMem) (s : Cpu) : Prop :=
  s.regs.get .r14 = L.buf ∧ s.regs.get .rbx = L.cb ∧ CbOk L s.mem ∧ VIRBridge.Rep wm s.mem L.live

/-- The driver's view after a return: `rip` at its return address, `rsp` one slot above the stub's frame, STATUS = `code`. -/
def Returned (L : Lay3) (code : W) (s : Cpu) : Prop :=
  s.stopped = false ∧ s.rip = L.ret0 ∧ s.regs.get .rsp = L.rsp0 + 8 ∧ rd s.mem L.cb = code

/-- **R3**: a word state and word memory against a machine state, in program `p` built in context `C`. -/
def R3 (C : Ctx3) (p : Program) (L : Lay3) : WSt × WMem → Cpu → Prop
  | (.run c ρ k, wm), s =>
      s.stopped = false ∧ CodeAt C p s.rip (gen C s.rip c) ∧ Common L wm s ∧
      L.envLo.toNat ≤ (s.regs.get .r12).toNat ∧ (s.regs.get .r12).toNat + 8 * ρ.length ≤ L.envTop.toNat ∧
      WordsAt s.mem (s.regs.get .r12) ρ ∧
      Frames C p L s.mem (s.regs.get .rsp) (s.regs.get .r12) k ∧ L.stkLo.toNat ≤ (s.regs.get .rsp).toNat
  | (.done ws, wm), s =>
      Returned L stDone s ∧ Common L wm s ∧ s.regs.get .r13 = BitVec.ofNat 64 ws.length ∧ WordsAt s.mem L.buf ws
  | (.fault, wm), s => Returned L stFault s ∧ Common L wm s
  | (.ovf, wm), s => Returned L stOvf s ∧ Common L wm s

/-- S3-S's third exit: the driver sees RES (no word state corresponds; `s3_refines` bounds when it can occur). -/
def ResExit (L : Lay3) (s : Cpu) : Prop := Returned L stRes s

end S3
