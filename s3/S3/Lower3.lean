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
def blen0 (ilen : Op → Nat) : Op → Nat
  | .jcc _ _ => 6
  | .jmp (.rel _) => 5
  | .call (.rel _) => 5
  | .ret => 1
  | o => ilen o

/-- Clamped to at least one byte, so positivity needs no case split over `Op` (S3-E's 1 ≤ `ilen` premise is then a fact). -/
def blen (ilen : Op → Nat) (o : Op) : Nat := max 1 (blen0 ilen o)

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

/-- One arithmetic operator, its operands at BUF slots t and t+1 (loaded into rax and rcx), its result at t (S3-I). Register
    forms only: x86lean states the reg-reg equations for add, sub, cmp, and, or (and imul with any source). -/
def arithCode (C : Ctx3) (t : Nat) : AOp → List AI
  | .add => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .add .q (.reg .rax) (.reg .rcx)), .jccA .o C.ovf,
      st .r14 (slot t) .rax]
  | .sub => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .sub .q (.reg .rax) (.reg .rcx)), .jccA .o C.ovf,
      st .r14 (slot t) .rax]
  | .mul => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.imulr .q .rax (.reg .rcx) none), .jccA .o C.ovf,
      st .r14 (slot t) .rax]
  | .lt => [movi .rdx 0, ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
      .op (.setcc .l (.reg .rdx)), st .r14 (slot t) .rdx]
  | .le => [movi .rdx 0, ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
      .op (.setcc .le (.reg .rdx)), st .r14 (slot t) .rdx]
  | .eq => [movi .rdx 0, ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
      .op (.setcc .e (.reg .rdx)), st .r14 (slot t) .rdx]
  | .max => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
      .op (.cmov .le .q .rax (.reg .rcx)), st .r14 (slot t) .rax]
  | .band => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .and .q (.reg .rax) (.reg .rcx)),
      st .r14 (slot t) .rax]
  | .bor => [ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .or .q (.reg .rax) (.reg .rcx)),
      st .r14 (slot t) .rax]

/-- Copy BUF slots `s..s+n` to `d..d+n`, ascending (safe for a move DOWN, `d ≤ s`). -/
def moves (s d : Nat) : Nat → List AI
  | 0 => []
  | n + 1 => moves s d n ++ [ld .rax .r14 (slot (s + n)), st .r14 (slot (d + n)) .rax]

/-- **evalTo t o**: code leaving `o`'s `wid o` words at BUF slots t, t+1, … (S3-L). Scratch above them is unconstrained. -/
def evalTo (C : Ctx3) : Nat → WOpd → List AI
  | t, .slice off len => (List.range len).flatMap fun j => [ld .rax .r12 (slot (off + j)), st .r14 (slot (t + j)) .rax]
  | t, .imm ws => (List.range ws.length).flatMap fun j => [movi .rax (ws.getD j 0), st .r14 (slot (t + j)) .rax]
  | t, .arith op a b => evalTo C t a ++ evalTo C (t + 1) b ++ arithCode C t op
  | t, .bnot a => evalTo C t a ++
      [movi .rax 1, ld .rcx .r14 (slot t), .op (.bin .sub .q (.reg .rax) (.reg .rcx)), st .r14 (slot t) .rax]
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
  [ld .rcx .rbx 16, .op (.mov .q (.reg .rax) (.reg .r12)), .op (.bin .sub .q (.reg .rax) (.reg .rcx)),
   .op (.bin .cmp .q (.reg .rax) (.imm (slot n))), .jccA .b C.res]

/-- Prepend BUF slots s..s+n to ρ (a static count): room check, `r12 −= 8n`, then the copies. -/
def prependBuf (C : Ctx3) (s n : Nat) : List AI :=
  envRoom C n ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot n) })] ++
    (List.range n).flatMap fun j => [ld .rax .r14 (slot (s + j)), st .r12 (slot j) .rax]

/-- STACK room for one pending `letE` (16 bytes: the saved envLow and the return address). -/
def stackRoom (C : Ctx3) : List AI :=
  [ld .rcx .rbx 24, .op (.mov .q (.reg .rax) (.reg .rsp)), .op (.bin .sub .q (.reg .rax) (.reg .rcx)),
   .op (.bin .cmp .q (.reg .rax) (.imm 16)), .jccA .b C.res]

/-- The RUNTIME prepend after a `letE` returns (Addendum 1): r13 words from BUF, by a loop. Placed at `pc`. -/
def prependLoop (C : Ctx3) (pc : W) : List AI :=
  let pre : List AI :=
    [ld .rdx .rbx 16, .op (.mov .q (.reg .rax) (.reg .r12)), .op (.bin .sub .q (.reg .rax) (.reg .rdx)),
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
       .op (.lea .q .rax { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .r14 (slot 1), st .rax 0 .rdx] ++
      envRoom C 2 ++ [ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
        .op (.lea .q .r12 { base := some .r12, disp := -(slot 2) }), st .r12 0 .rcx, st .r12 (slot 1) .rdx]
    pre ++ gen C (pc + BitVec.ofNat 64 (bytes C pre)) k
  | pc, .app f x =>
    let pre := evalTo C (need x) f ++ evalTo C 0 x ++ [ld .rdx .r14 (slot (need x)), ld .r12 .rsp 8]
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

/-- The whole program's code, CONTIGUOUS from the code base: entry stub, FAULT, OVF, RES, main, then the table's bodies in order. -/
def allCode (C : Ctx3) (tbl : Table) (main : WCode) : List AI :=
  entryStub (mainAddr C) ++ exitCode stFault ++ exitCode stOvf ++ exitCode stRes ++ gen C (mainAddr C) main ++
    tbl.zipIdx.flatMap fun p => gen C (C.body p.2) p.1.2

/-- **lower3**: the x86lean `Program` for a word program: table `tbl`, main code `main`, code base `base`. -/
def lower3 (ilen : Op → Nat) (tbl : Table) (main : WCode) (base : W) : Program :=
  let C := ctxOf ilen tbl main base
  { code := asm C base (allCode C tbl main) }

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
       .op (.lea .q .rax { base := some .rcx, index := some .rax, scale := .s8 }), ld .rdx .r14 (slot 1), st .rax 0 .rdx] ++
      envRoom C 2 ++ [ld .rcx .r12 (slot off), ld .rdx .r12 (slot (off + 1)),
        .op (.lea .q .r12 { base := some .r12, disp := -(slot 2) }), st .r12 0 .rcx, st .r12 (slot 1) .rdx]) +
      gsz C k
  | .app f x => bytes C (evalTo C (need x) f ++ evalTo C 0 x ++ [ld .rdx .r14 (slot (need x)), ld .r12 .rsp 8]) +
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

/-! ## Placement: every instruction of a piece is fetched at its address -/

theorem ofNat_add64 (x y : Nat) : BitVec.ofNat 64 (x + y) = BitVec.ofNat 64 x + BitVec.ofNat 64 y := by
  rw [BitVec.ofNat_add_ofNat]

theorem asm_append (C : Ctx3) : ∀ (pc : W) (a b : List AI),
    asm C pc (a ++ b) = asm C pc a ++ asm C (pc + BitVec.ofNat 64 (bytes C a)) b
  | pc, [], b => by simp [asm, bytes_nil]
  | pc, i :: a, b => by
      simp only [List.cons_append, asm, bytes_cons, asm_append C _ a b, ofNat_add64, BitVec.add_assoc]

theorem asm_length (C : Ctx3) : ∀ (pc : W) (l : List AI), (asm C pc l).length = l.length
  | _, [] => rfl
  | pc, _ :: l => by simp [asm, asm_length C _ l]

/-- The address of instruction j of a list placed at `pc`. -/
def addrAt (C : Ctx3) (pc : W) (l : List AI) (j : Nat) : W := pc + BitVec.ofNat 64 (bytes C (l.take j))

theorem asm_getElem (C : Ctx3) : ∀ (pc : W) (l : List AI) (j : Nat) (h : j < l.length),
    (asm C pc l)[j]'(by rw [asm_length]; exact h) = (addrAt C pc l j, l[j].toInstr C (addrAt C pc l j))
  | pc, i :: l, 0, _ => by simp [asm, addrAt, bytes_nil]
  | pc, i :: l, j + 1, h => by
      simp only [asm, List.getElem_cons_succ]
      rw [asm_getElem C _ l j (by simp at h; omega)]
      simp only [addrAt, List.take_succ_cons, bytes_cons, ofNat_add64, BitVec.add_assoc]

/-- Every instruction has size at least 1 under S3-E's premise on `ilen`. -/
theorem size_pos {C : Ctx3} (hC : ∀ o, 1 ≤ C.ilen o) (i : AI) : 1 ≤ AI.size C i := by
  cases i with
  | op o => simp only [AI.size, blen]; exact Nat.le_max_left _ _
  | _ => simp [AI.size]

theorem bytes_take_lt {C : Ctx3} (hC : ∀ o, 1 ≤ C.ilen o) : ∀ (l : List AI) (j k : Nat), j < k → k ≤ l.length →
    bytes C (l.take j) < bytes C (l.take k)
  | [], _, _, h, hk => by simp at hk; omega
  | i :: l, 0, k + 1, _, _ => by
      simp only [List.take_zero, bytes_nil, List.take_succ_cons, bytes_cons]; have := size_pos hC i; omega
  | i :: l, j + 1, k + 1, h, hk => by
      simp only [List.take_succ_cons, bytes_cons]
      have := bytes_take_lt hC l j k (by omega) (by simp at hk; omega); omega
  | _ :: _, _, 0, h, _ => absurd h (Nat.not_lt_zero _)

theorem bytes_take_le (C : Ctx3) : ∀ (l : List AI) (j : Nat), bytes C (l.take j) ≤ bytes C l
  | [], _ => by simp
  | i :: l, 0 => by simp [bytes_nil]
  | i :: l, j + 1 => by simp only [List.take_succ_cons, bytes_cons]; have := bytes_take_le C l j; omega

/-- Addresses within one placed list are distinct when its size fits the address space. -/
theorem asm_nodup {C : Ctx3} (hC : ∀ o, 1 ≤ C.ilen o) (pc : W) (l : List AI) (hb : bytes C l < 2 ^ 64) :
    ((asm C pc l).map Prod.fst).Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro j k hjk hk
  simp only [List.length_map, asm_length] at hk
  rw [List.getElem?_eq_getElem (by simp [asm_length]; omega), List.getElem?_eq_getElem (by simp [asm_length]; omega)]
  simp only [List.getElem_map, ne_eq, Option.some.injEq]
  rw [asm_getElem C pc l j (by omega), asm_getElem C pc l k hk]
  simp only [addrAt]
  intro he
  have hlt := bytes_take_lt hC l j k hjk (by omega)
  have hle := bytes_take_le C l k
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have hp := pc.isLt
  omega

theorem at?_of_nodup {p : Program} {a : W} {i : Instr} (hn : (p.code.map Prod.fst).Nodup) (hm : (a, i) ∈ p.code) :
    p.at? a = some i := by
  obtain ⟨code⟩ := p
  simp only [Program.at?]
  induction code with
  | nil => simp at hm
  | cons q rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.find?_cons]
    by_cases hq : q.1 = a
    · simp only [hq, beq_self_eq_true, Option.map_some]
      rcases List.mem_cons.mp hm with h | h
      · rw [← h]
      · exact absurd (hq ▸ List.mem_map_of_mem (f := Prod.fst) h) hn.1
    · have : (q.1 == a) = false := by simp [hq]
      rw [this]
      rcases List.mem_cons.mp hm with h | h
      · exact absurd (by rw [← h]) hq
      · exact ih hn.2 h

/-- **CodeAt**: every instruction of `l`, placed at `pc`, is what `p` fetches at its address. -/
def CodeAt (C : Ctx3) (p : Program) (pc : W) (l : List AI) : Prop :=
  ∀ j (h : j < l.length), p.at? (addrAt C pc l j) = some (l[j].toInstr C (addrAt C pc l j))

theorem codeAt_asm {C : Ctx3} (hC : ∀ o, 1 ≤ C.ilen o) (pc : W) (l : List AI) (hb : bytes C l < 2 ^ 64) :
    CodeAt C { code := asm C pc l } pc l := by
  intro j h
  apply at?_of_nodup (asm_nodup hC pc l hb)
  rw [← asm_getElem C pc l j h]
  exact List.getElem_mem _

theorem codeAt_left {C : Ctx3} {p : Program} {pc : W} {a b : List AI} (h : CodeAt C p pc (a ++ b)) : CodeAt C p pc a := by
  intro j hj
  have := h j (by simp; omega)
  simp only [addrAt, List.take_append_of_le_length (Nat.le_of_lt hj), List.getElem_append_left hj] at this
  exact this

theorem codeAt_right {C : Ctx3} {p : Program} {pc : W} {a b : List AI} (h : CodeAt C p pc (a ++ b)) :
    CodeAt C p (pc + BitVec.ofNat 64 (bytes C a)) b := by
  intro j hj
  have := h (a.length + j) (by simp; omega)
  simp only [addrAt, List.take_length_add_append, bytes_append, ofNat_add64, BitVec.add_assoc] at this
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  simpa only [addrAt, BitVec.add_assoc] using this

end S3
