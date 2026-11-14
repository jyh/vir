/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, S3-I/K/R/X/D, Addendum 1, Addendum 2): word code → x86lean instructions.
  Code is generated as `AI`s, instructions whose branch targets are ABSOLUTE addresses. `asm` places a list at an address and turns
  each target into the rel32 displacement x86lean's `jcc`/`jmp`/`call` carry. Lengths follow S3-E: `ilen` is a parameter, and every
  branch uses its fixed-length rel32 form, so no code size depends on an address (`bytes_gen` is the fact the placement needs).
  Register map (S3-M): r12 envLow · r13 result count · r14 BUF · rbx the control block · rax rcx rdx temporaries.
-/
import S3.Frame
import X86.Program

namespace S3
open VIRC X86

/-- An instruction with an absolute branch target (S3-L). -/
inductive AI where
  | op (o : Op)
  | jccA (c : Cc) (a : W)
  | jmpA (a : W)
  | callA (a : W)

/-- The status words (S3-X): DONE 0, FAULT 1, OVF 2, RES 3. -/
def stDone : W := 0
def stFault : W := 1
def stOvf : W := 2
def stRes : W := 3

/-- The context code is generated in: the length parameter, the exits, and the function table's body addresses and fix flags. -/
structure Ctx3 where
  ilen : Op → Nat
  fault : W
  ovf : W
  res : W
  body : Nat → W
  fix : Nat → Bool
  tblLen : Nat

/-- S3-E: an instruction's length. Branches are rel32 forms of fixed length; everything else is `ilen`. -/
def blen (ilen : Op → Nat) : Op → Nat
  | .jcc _ _ => 6
  | .jmp (.rel _) => 5
  | .call (.rel _) => 5
  | .ret => 1
  | o => ilen o

def AI.size (C : Ctx3) : AI → Nat
  | .op o => blen C.ilen o
  | .jccA _ _ => 6
  | .jmpA _ => 5
  | .callA _ => 5

def bytes (C : Ctx3) (l : List AI) : Nat := (l.map (AI.size C)).sum

/-- One instruction placed at `pc`: its rel32 displacement is measured from the next instruction. -/
def AI.toInstr (C : Ctx3) (pc : W) : AI → Instr
  | .op o => ⟨o, blen C.ilen o⟩
  | .jccA c a => ⟨.jcc c (a - (pc + 6)), 6⟩
  | .jmpA a => ⟨.jmp (.rel (a - (pc + 5))), 5⟩
  | .callA a => ⟨.call (.rel (a - (pc + 5))), 5⟩

/-- Place a list at `pc`. -/
def asm (C : Ctx3) : W → List AI → List (W × Instr)
  | _, [] => []
  | pc, i :: is => (pc, i.toInstr C pc) :: asm C (pc + BitVec.ofNat 64 (i.size C)) is

/-! ## Operand forms -/

def memAt (b : GPR) (d : W) : Operand := .mem { base := some b, disp := d }
def ld (r b : GPR) (d : W) : AI := .op (.mov .q (.reg r) (memAt b d))
def st (b : GPR) (d : W) (r : GPR) : AI := .op (.mov .q (memAt b d) (.reg r))
def movi (r : GPR) (v : W) : AI := .op (.mov .q (.reg r) (.imm v))
/-- The byte offset of word slot `t`. -/
def slot (t : Nat) : W := BitVec.ofNat 64 (8 * t)

/-- One arithmetic operator, its operands at BUF slots t and t+1, its result at t (S3-I). -/
def arithCode (C : Ctx3) (t : Nat) : AOp → List AI
  | .add => [ld .rax .r14 (slot t), .op (.bin .add .q (.reg .rax) (memAt .r14 (slot (t + 1)))), .jccA .o C.ovf, st .r14 (slot t) .rax]
  | .sub => [ld .rax .r14 (slot t), .op (.bin .sub .q (.reg .rax) (memAt .r14 (slot (t + 1)))), .jccA .o C.ovf, st .r14 (slot t) .rax]
  | .mul => [ld .rax .r14 (slot t), .op (.imulr .q .rax (memAt .r14 (slot (t + 1))) none), .jccA .o C.ovf, st .r14 (slot t) .rax]
  | .lt => [movi .rcx 0, ld .rax .r14 (slot t), .op (.bin .cmp .q (.reg .rax) (memAt .r14 (slot (t + 1)))),
      .op (.setcc .l (.reg .rcx)), st .r14 (slot t) .rcx]
  | .le => [movi .rcx 0, ld .rax .r14 (slot t), .op (.bin .cmp .q (.reg .rax) (memAt .r14 (slot (t + 1)))),
      .op (.setcc .le (.reg .rcx)), st .r14 (slot t) .rcx]
  | .eq => [movi .rcx 0, ld .rax .r14 (slot t), .op (.bin .cmp .q (.reg .rax) (memAt .r14 (slot (t + 1)))),
      .op (.setcc .e (.reg .rcx)), st .r14 (slot t) .rcx]
  | .max => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
      .op (.cmov .le .q .rax (.reg .rcx)), st .r14 (slot t) .rax]
  | .band => [ld .rax .r14 (slot t), .op (.bin .and .q (.reg .rax) (memAt .r14 (slot (t + 1)))), st .r14 (slot t) .rax]
  | .bor => [ld .rax .r14 (slot t), .op (.bin .or .q (.reg .rax) (memAt .r14 (slot (t + 1)))), st .r14 (slot t) .rax]

/-- Copy BUF slots `s..s+n` to `d..d+n`, ascending (safe for a move DOWN, `d ≤ s`). -/
def moves (s d : Nat) : Nat → List AI
  | 0 => []
  | n + 1 => moves s d n ++ [ld .rax .r14 (slot (s + n)), st .r14 (slot (d + n)) .rax]

/-- **evalTo t o**: code leaving `o`'s `wid o` words at BUF slots t, t+1, … (S3-L). Scratch above them is unconstrained. -/
def evalTo (C : Ctx3) : Nat → WOpd → List AI
  | t, .slice off len => (List.range len).flatMap fun j => [ld .rax .r12 (slot (off + j)), st .r14 (slot (t + j)) .rax]
  | t, .imm ws => ws.zipIdx.flatMap fun p => [movi .rax p.1, st .r14 (slot (t + p.2)) .rax]
  | t, .arith op a b => evalTo C t a ++ evalTo C (t + 1) b ++ arithCode C t op
  | t, .bnot a => evalTo C t a ++ [movi .rax 1, .op (.bin .sub .q (.reg .rax) (memAt .r14 (slot t))), st .r14 (slot t) .rax]
  | t, .cat a b => evalTo C t a ++ evalTo C (t + wid a) b
  | t, .take _ a => evalTo C t a
  | t, .drop n a => evalTo C t a ++ moves (t + n) t (wid a - n)
  | t, .tag tg pad a => evalTo C (t + 1) a ++ [movi .rax tg, st .r14 (slot t) .rax, movi .rax 0] ++
      (List.range pad).flatMap fun j => [st .r14 (slot (t + 1 + wid a + j)) .rax]

/-- BUF slots an operand evaluated at slot 0 touches (S3-L's `need`; `Fragment3.ok` bounds it by BUF's size). -/
def need : WOpd → Nat
  | .slice _ len => len
  | .imm ws => ws.length
  | .arith _ a b => max (max (need a) (1 + need b)) 2
  | .bnot a => max (need a) 1
  | .cat a b => max (need a) (wid a + need b)
  | .take _ a => need a
  | .drop _ a => need a
  | .tag _ pad a => max (1 + need a) (1 + wid a + pad)

/-! ## ENV and STACK -/

/-- ENV room check for `n` words (S3-S): RES unless `r12 − envLo ≥ 8n`. Clobbers rax. -/
def envRoom (C : Ctx3) (n : Nat) : List AI :=
  [.op (.mov .q (.reg .rax) (.reg .r12)), .op (.bin .sub .q (.reg .rax) (memAt .rbx 16)),
   .op (.bin .cmp .q (.reg .rax) (.imm (slot n))), .jccA .b C.res]

/-- Prepend BUF slots s..s+n to ρ (a static count): room check, `r12 −= 8n`, then the copies. -/
def prependBuf (C : Ctx3) (s n : Nat) : List AI :=
  envRoom C n ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot n) })] ++
    (List.range n).flatMap fun j => [ld .rax .r14 (slot (s + j)), st .r12 (slot j) .rax]

/-- STACK room for one pending `letE` (16 bytes: the saved envLow and the return address). -/
def stackRoom (C : Ctx3) : List AI :=
  [.op (.mov .q (.reg .rax) (.reg .rsp)), .op (.bin .sub .q (.reg .rax) (memAt .rbx 24)),
   .op (.bin .cmp .q (.reg .rax) (.imm 16)), .jccA .b C.res]

/-- The RUNTIME prepend after a `letE` returns (Addendum 1): r13 words from BUF, by a loop. Placed at `pc`. -/
def prependLoop (C : Ctx3) (pc : W) : List AI :=
  let pre : List AI :=
    [.op (.mov .q (.reg .rax) (.reg .r12)), .op (.bin .sub .q (.reg .rax) (memAt .rbx 16)),
     .op (.lea .q .rcx { index := some .r13, scale := .s8 }), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)), .jccA .b C.res,
     .op (.bin .sub .q (.reg .r12) (.reg .rcx)), movi .rcx 0]
  let head := pc + BitVec.ofNat 64 (bytes C pre)
  let body : List AI :=
    [.op (.mov .q (.reg .rax) (.mem { base := some .r14, index := some .rcx, scale := .s8 })),
     .op (.mov .q (.mem { base := some .r12, index := some .rcx, scale := .s8 }) (.reg .rax)),
     .op (.bin .add .q (.reg .rcx) (.imm 1))]
  let test : List AI := [.op (.bin .cmp .q (.reg .rcx) (.reg .r13))]
  let exit := head + BitVec.ofNat 64 (bytes C test + 6 + bytes C body + 5)
  pre ++ test ++ [.jccA .ae exit] ++ body ++ [.jmpA head]

/-- One entry of `app`'s dispatch chain (S3-D (a)): label in rdx, x's `wx` words at BUF 0.. . -/
def dispatchEntry (C : Ctx3) (wx i : Nat) (next : W) : List AI :=
  let n := if C.fix i then wx + 1 else wx
  [.op (.bin .cmp .q (.reg .rdx) (.imm (BitVec.ofNat 64 i))), .jccA .ne next] ++
    envRoom C n ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot n) })] ++
    (List.range wx).flatMap (fun j => [ld .rax .r14 (slot j), st .r12 (slot j) .rax]) ++
    (if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ [.jmpA (C.body i)]

/-- The chain from entry `i` on, placed at `pc`; past the table it jumps to FAULT (a BAD label: S2 has no step, nothing claimed). -/
def dispatch (C : Ctx3) (wx : Nat) (pc : W) : Nat → Nat → List AI
  | 0, _ => [.jmpA C.fault]
  | fuel + 1, i =>
    let sz := bytes C (dispatchEntry C wx i 0)
    dispatchEntry C wx i (pc + BitVec.ofNat 64 sz) ++ dispatch C wx (pc + BitVec.ofNat 64 sz) fuel (i + 1)

/-! ## Code -/

/-- **gen C pc c**: the code for `c` placed at `pc`, its out-of-line parts included and contiguous (S3-L). -/
def gen (C : Ctx3) : W → WCode → List AI
  | _, .ret o => evalTo C 0 o ++ [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret]
  | pc, .letE c₁ c₂ =>
    let pre := stackRoom C ++ [.op (.push .q (.reg .r12))]
    let pAfter := pc + BitVec.ofNat 64 (bytes C pre + 5)
    let post := [.op (.pop .q (.reg .r12))] ++ prependLoop C (pAfter + BitVec.ofNat 64 (bytes C [.op (.pop .q (.reg .r12))]))
    let p₂ := pAfter + BitVec.ofNat 64 (bytes C post)
    let g₂ := gen C p₂ c₂
    let p₁ := p₂ + BitVec.ofNat 64 (bytes C g₂)
    pre ++ [.callA p₁] ++ post ++ g₂ ++ gen C p₁ c₁
  | pc, .load off idx k =>
    let pre := evalTo C 0 idx ++
      [ld .rax .r14 (slot 0), ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
       .op (.bin .test .q (.reg .rax) (.reg .rax)), .jccA .s C.fault,
       .op (.bin .cmp .q (.reg .rax) (.reg .rdx)), .jccA .ge C.fault,
       .op (.lea .q .rcx { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .rcx 0] ++
      envRoom C 1 ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot 1) }), st .r12 0 .rdx]
    pre ++ gen C (pc + BitVec.ofNat 64 (bytes C pre)) k
  | pc, .store off idx v k =>
    let pre := evalTo C 0 idx ++ evalTo C 1 v ++
      [ld .rax .r14 (slot 0), ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
       .op (.bin .test .q (.reg .rax) (.reg .rax)), .jccA .s C.fault,
       .op (.bin .cmp .q (.reg .rax) (.reg .rdx)), .jccA .ge C.fault,
       .op (.lea .q .rax { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .r14 (slot 1), st .rax 0 .rdx,
       ld .rdx .r12 (slot (off + 1))] ++
      envRoom C 2 ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot 2) }), st .r12 0 .rcx, st .r12 (slot 1) .rdx]
    pre ++ gen C (pc + BitVec.ofNat 64 (bytes C pre)) k
  | pc, .app f x =>
    let pre := evalTo C 0 f ++ [ld .rdx .r14 (slot 0)] ++ evalTo C 0 x ++ [ld .r12 .rsp 8]
    pre ++ dispatch C (wid x) (pc + BitVec.ofNat 64 (bytes C pre)) C.tblLen 0
  | pc, .ite o c₁ c₂ =>
    let pre := evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 1))]
    let p₁ := pc + BitVec.ofNat 64 (bytes C pre + 6)
    let g₁ := gen C p₁ c₁
    let l₂ := p₁ + BitVec.ofNat 64 (bytes C g₁)
    let mid := [.op (.bin .cmp .q (.reg .rax) (.imm 0)), .jccA .ne C.fault]
    pre ++ [.jccA .ne l₂] ++ g₁ ++ mid ++ gen C (l₂ + BitVec.ofNat 64 (bytes C mid)) c₂
  | pc, .case o n₁ n₂ c₁ c₂ =>
    let w := wid o - 1
    let pre := evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 0))]
    let pb₁ := prependBuf C 1 (min n₁ w)
    let p₁ := pc + BitVec.ofNat 64 (bytes C pre + 6 + bytes C pb₁)
    let g₁ := gen C p₁ c₁
    let l₂ := p₁ + BitVec.ofNat 64 (bytes C g₁)
    let mid := [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault] ++ prependBuf C 1 (min n₂ w)
    pre ++ [.jccA .ne l₂] ++ pb₁ ++ g₁ ++ mid ++ gen C (l₂ + BitVec.ofNat 64 (bytes C mid)) c₂

/-! ## The program -/

/-- An exit (S3-X (a)): STATUS := code, `rsp` := the saved driver `rsp`, `ret` to the driver. -/
def exitCode (code : W) : List AI := [movi .rax code, st .rbx 0 .rax, ld .rsp .rbx 8, .op .ret]

/-- The entry stub (Addendum 2): save `rsp`, push r12 (so `[rsp + 8]` is the activation base), call the main code; DONE on return. -/
def entryStub (main : W) : List AI :=
  [st .rbx 8 .rsp, .op (.push .q (.reg .r12)), .callA main, .op (.pop .q (.reg .r12)),
   movi .rax stDone, st .rbx 0 .rax, .op .ret]

/-- The pieces' addresses from `base`: entry stub, FAULT, OVF, RES, main, then each table body in order. Sizes come from a
    first generation in `C0` (S3-E: no size depends on an address or a target, `bytes_gen` below). -/
def bodyAddrs (C0 : Ctx3) (tbl : Table) (start : W) : List W :=
  (tbl.foldl (fun (acc : List W × W) (e : Bool × WCode) =>
    (acc.1 ++ [acc.2], acc.2 + BitVec.ofNat 64 (bytes C0 (gen C0 acc.2 e.2))))
    ([], start)).1

/-- The whole layout context for `tbl` with main code `main` at code base `base`. -/
def ctxOf (ilen : Op → Nat) (tbl : Table) (main : WCode) (base : W) : Ctx3 :=
  let C0 : Ctx3 :=
    { ilen := ilen
      fault := 0
      ovf := 0
      res := 0
      body := fun _ => 0
      fix := fun i => (tbl[i]?.map (·.1)).getD false
      tblLen := tbl.length }
  let pF := base + BitVec.ofNat 64 (bytes C0 (entryStub 0))
  let pO := pF + BitVec.ofNat 64 (bytes C0 (exitCode stFault))
  let pR := pO + BitVec.ofNat 64 (bytes C0 (exitCode stOvf))
  let pM := pR + BitVec.ofNat 64 (bytes C0 (exitCode stRes))
  let C1 : Ctx3 := { C0 with fault := pF, ovf := pO, res := pR }
  let pB := pM + BitVec.ofNat 64 (bytes C0 (gen C0 pM main))
  let bs := bodyAddrs C1 tbl pB
  { C1 with body := fun i => bs.getD i 0 }

/-- The main code's address in a layout (the entry stub's call target). -/
def mainAddr (C : Ctx3) : W := C.res + BitVec.ofNat 64 (bytes C (exitCode stRes))

/-- **lower3**: the x86lean `Program` for a word program: table `tbl`, main code `main`, code base `base`. -/
def lower3 (ilen : Op → Nat) (tbl : Table) (main : WCode) (base : W) : Program :=
  let C := ctxOf ilen tbl main base
  let pM := mainAddr C
  let pieces : List (W × List AI) :=
    [(base, entryStub pM), (C.fault, exitCode stFault), (C.ovf, exitCode stOvf), (C.res, exitCode stRes),
     (pM, gen C pM main)] ++ (tbl.zipIdx.map fun p => (C.body p.2, gen C (C.body p.2) p.1.2))
  { code := pieces.flatMap fun p => asm C p.1 p.2 }

/-! ## S3-E's consequence: a sub-term's code size is a function of the sub-term (`bytes_gen`), and of the context only through
    `ilen`, the fix flags and the table size (`gsz_congr`). The placement in `ctxOf` rests on both. -/

theorem bytes_nil (C : Ctx3) : bytes C [] = 0 := rfl
theorem bytes_cons (C : Ctx3) (i : AI) (l : List AI) : bytes C (i :: l) = AI.size C i + bytes C l := by
  simp [bytes]
theorem bytes_append (C : Ctx3) (a b : List AI) : bytes C (a ++ b) = bytes C a + bytes C b := by
  simp [bytes]
theorem bytes_flatMap {α} (C : Ctx3) (l : List α) (f : α → List AI) :
    bytes C (l.flatMap f) = (l.map fun x => bytes C (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, bytes_append, ih]

/-- The dispatch chain's size: its entries (each sized with a dummy successor) and the final jump. -/
def dsz (C : Ctx3) (wx : Nat) : Nat → Nat → Nat
  | 0, _ => 5
  | fuel + 1, i => bytes C (dispatchEntry C wx i 0) + dsz C wx fuel (i + 1)

theorem bytes_dispatchEntry (C : Ctx3) (wx i : Nat) (nx : W) :
    bytes C (dispatchEntry C wx i nx) = bytes C (dispatchEntry C wx i 0) := by
  simp only [dispatchEntry, bytes_append, bytes_cons, AI.size]

theorem bytes_dispatch (C : Ctx3) (wx : Nat) : ∀ (fuel i : Nat) (pc : W), bytes C (dispatch C wx pc fuel i) = dsz C wx fuel i
  | 0, _, _ => rfl
  | fuel + 1, i, pc => by
      simp only [dispatch, dsz, bytes_append, bytes_dispatchEntry C wx i, bytes_dispatch C wx fuel (i + 1)]

theorem bytes_prependLoop (C : Ctx3) (pc : W) : bytes C (prependLoop C pc) = bytes C (prependLoop C 0) := by
  simp only [prependLoop, bytes_append, bytes_cons, AI.size]

/-- A code size, structurally. -/
def gsz (C : Ctx3) : WCode → Nat
  | .ret o => bytes C (evalTo C 0 o) + bytes C [movi .r13 (BitVec.ofNat 64 (wid o)), .op .ret]
  | .letE c₁ c₂ => bytes C (stackRoom C ++ [.op (.push .q (.reg .r12))]) + 5 +
      bytes C ([.op (.pop .q (.reg .r12))] ++ prependLoop C 0) + gsz C c₂ + gsz C c₁
  | .load off idx k => bytes C (evalTo C 0 idx ++
      [ld .rax .r14 (slot 0), ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
       .op (.bin .test .q (.reg .rax) (.reg .rax)), .jccA .s C.fault,
       .op (.bin .cmp .q (.reg .rax) (.reg .rdx)), .jccA .ge C.fault,
       .op (.lea .q .rcx { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .rcx 0] ++
      envRoom C 1 ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot 1) }), st .r12 0 .rdx]) + gsz C k
  | .store off idx v k => bytes C (evalTo C 0 idx ++ evalTo C 1 v ++
      [ld .rax .r14 (slot 0), ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
       .op (.bin .test .q (.reg .rax) (.reg .rax)), .jccA .s C.fault,
       .op (.bin .cmp .q (.reg .rax) (.reg .rdx)), .jccA .ge C.fault,
       .op (.lea .q .rax { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .r14 (slot 1), st .rax 0 .rdx,
       ld .rdx .r12 (slot (off + 1))] ++
      envRoom C 2 ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot 2) }), st .r12 0 .rcx, st .r12 (slot 1) .rdx]) +
      gsz C k
  | .app f x => bytes C (evalTo C 0 f ++ [ld .rdx .r14 (slot 0)] ++ evalTo C 0 x ++ [ld .r12 .rsp 8]) +
      dsz C (wid x) C.tblLen 0
  | .ite o c₁ c₂ => bytes C (evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 1))]) + 6 +
      gsz C c₁ + bytes C [.op (.bin .cmp .q (.reg .rax) (.imm 0)), .jccA .ne C.fault] + gsz C c₂
  | .case o n₁ n₂ c₁ c₂ => bytes C (evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 0))]) + 6 +
      bytes C (prependBuf C 1 (min n₁ (wid o - 1))) + gsz C c₁ +
      bytes C ([.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault] ++ prependBuf C 1 (min n₂ (wid o - 1))) + gsz C c₂

/-- **bytes_gen.** The code for `c` at any address has size `gsz C c`. -/
theorem bytes_gen (C : Ctx3) : ∀ (c : WCode) (pc : W), bytes C (gen C pc c) = gsz C c
  | .ret o, _ => by simp only [gen, gsz, bytes_append]
  | .letE c₁ c₂, pc => by
      simp only [gen, gsz, bytes_append, bytes_gen C c₂, bytes_gen C c₁, bytes_prependLoop C, bytes_cons, bytes_nil, AI.size]
  | .load off idx k, pc => by simp only [gen, gsz, bytes_append, bytes_gen C k]
  | .store off idx v k, pc => by simp only [gen, gsz, bytes_append, bytes_gen C k]
  | .app f x, pc => by simp only [gen, gsz, bytes_append, bytes_dispatch]
  | .ite o c₁ c₂, pc => by
      simp only [gen, gsz, bytes_append, bytes_gen C c₁, bytes_gen C c₂, bytes_cons, bytes_nil, AI.size]
  | .case o n₁ n₂ c₁ c₂, pc => by
      simp only [gen, gsz, bytes_append, bytes_gen C c₁, bytes_gen C c₂, bytes_cons, bytes_nil, AI.size]

end S3
