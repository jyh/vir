# OBJECT-COMPILER — the VIR → x86-64 compiler for L2 programs (C0(a) C1(a) C2(a) C3(a); C4 declared at the pin)

**Drafted 2026-11-06 by the 29th vir head. PINNED 2026-11-11 by the 61st, BEFORE any compiler file**, on the Captain's word at
the 11-11 council (ask 4; *"yes accept"*, the same word that pins OBJECT-DEFLATE). C0 (a) DEFLATE first with a generic verified
driver · C1 (a) a verified compiler, with translation validation as a per-stage fallback that is declared when used · C2 (a)
first-order L2, rejected by a checked predicate otherwise · C3 (a) the instruction library is public x86lean work (paris's).
He accepted without having read this text. One word from him at any sitting re-opens the choice of first program.
**This is a departure from O95's named first program**, the message router. That departure was put to him beside the
recommendation, and it is recorded here so that no reader takes DEFLATE for the router's successor by default.
The text from "The draft's own preamble" down is the draft byte for byte, except three redactions: two bus offsets (`@[bus]`)
and one pointer to the fleet's private record. **Nothing in this file is edited after its pin.** An erratum goes in
`errata/ERRATA-COMPILER.md`. Predictions: `predictions/PREDICTIONS-amend-23.md` §K, in this file's commit.

**Declared at the pin, against §1 and §3 below. Each is a fact read at master 1189b49 and x86lean origin/master 5f2231f:**
- **C4, a fork the draft MISSED: `int` is the unbounded `Int` (`l1/VIRL1/L1.lean:12`), while S2 makes values 64-bit words.**
  `add`/`sub`/`mul` can therefore leave the word on a run that ⟶₂ completes. The plan's own "what would show this wrong" forbids
  the FAULT exit on such a run, and it is silent about a WRONG ANSWER. The arms: (a) a per-run premise that every int lies in
  [−2⁶³, 2⁶³), discharged program by program; (b) CHECKED arithmetic: an overflow jumps to a SECOND exit, distinct from the
  fault exit. The theorem then reads "the machine matches ⟶₂, or it stops at the overflow exit", it never gives a wrong answer,
  and it carries no per-run premise. For a given program, separately, the overflow exit can be proved unreachable; (c) a
  bignum runtime. **vir takes (b), under the 08/31 law (a design fork proceeds on its recommendation, both arms posted)**. It
  is reversible until S2's first file, and posted to the helm at this pin. (c) adds a heap runtime that C2 (a) exists to avoid.
  (a) moves the gap into every program's proof.
- **§3's instruction list omits `imul`**, which L1's `mul` needs, and a `setcc` (or branch) form, which `lt`/`le`/`eq` need to
  produce a boolean value. Both are on x86lean's differentially-tested list (`docs/COVERAGE.md` at 5f2231f: `imul` T-frame,
  `setcc` T-exact). So are every mnemonic §3 names (`mov`, `movzx`, `lea`, `add`, `sub`, `and`, `or`, `xor`, `shl`, `shr`,
  `cmp`, `test`, `jcc`, `jmp`, `call`, `retq`) and `jo`, which C4 (b) needs and which is one of `jcc`'s 16 conditions.
- **L1/L2 have no shift or bitwise primitive** (OBJECT-DEFLATE's declaration). §3's `shl`/`shr`/`and`/`or`/`xor` are therefore
  instructions the COMPILER may use in its own runtime code (bounds checks, address arithmetic). They are not the image of any
  source operator.

The draft's own preamble, kept as its record:

# COMPILER PLAN — DRAFT, UNPINNED: the VIR → x86-64 compiler for L2 programs (his step 1; STATUS-vir row 169)

**Drafted 2026-11-06 ~12:4x PST by the 29th vir head**, on the helm's O83 fill (@[bus]). His words at the 11-06 sitting:
*"What are the next steps, e.g. 1) build the VIR compiler (using the sweva method), 2) build an application … However, #1
remains."* It is meant to be read with the MAP (vir f90a8e0) and the DEFLATE draft (the fleet's private record, same date) as one set. **Nothing
pins or freezes on this page.** Each fork has a recommendation and a default. Predictions are written after his "yes" and before
the first compiler file, in the same way as every layer so far.

## 0. What exists, and what is missing
- **Exists:** ONE hand lowering. A.4 (as repaired) is proved against x86lean for program 1 (paris's spike `repaired_refines`),
  and `compose/` joins it to the specification as one term, U → x86 (`lowered_refines_U`, RESULTS-3). Two calls compose
  (`two_emits_same_sender`). x86lean has a program-indexed step relation `stepP`, which can express a loop (X86/Program.lean,
  council 09-10 ⑧). It has no decoder: "these bytes are this instruction" is trusted to Intel XED and recorded in its coverage
  table (x86lean README).
- **Missing:** a compiler, meaning a Lean function from L2 terms to x86lean programs, and one theorem covering every program it
  accepts. The spike's instruction lemmas (Router/Steps.lean) are private, written for one program, and cover only the forms the
  router uses.

## 1. The stages, and what is PROVED and what is TESTED at each one
```
  S0  a closed, ⊢₂-typed L2 program        meaning: ⟶₂ (and ⟦·⟧₂ where adequacy gives it)          SOURCE (exists, l2/)
  S1  → a first-order block IR (ANF)       PROVED: a forward simulation of ⟶₂; L2 is deterministic,
                                           so it gives refinement in both directions
  S2  → layout: regions become address     PROVED: simulation, under a DISJOINTNESS + BOUNDS premise
      ranges, values become 64-bit words   discharged by the capabilities (the frame rule's reading).
      and byte cells                       An index fault lowers to an explicit bounds check that
                                           jumps to ONE fault exit, so a fault is an observable state
                                           and never undefined behaviour
  S3  → x86lean `Program` (instructions    PROVED: block-level simulation over `stepP`, from
      at addresses)                        per-instruction effect equations (the Router/Steps form)
  S4  → bytes (GNU as)                     TESTED, NOT PROVED: decode with XED and compare it with the
                                           S3 Program, then a differential run on hardware. This is the
                                           trust x86lean already declares, and the plan adds none
```
The theorem at the end is: for every program the compiler ACCEPTS, every ⟶₂ run is matched by a `stepP` run of the output
(including the fault exit), under the layout premise. Composing that with an L2 triple carries the triple to the machine.

## 2. The forks
- **C0 — L1′ (capabilities in function types) before DEFLATE?** The DEFLATE draft's X1 (a) makes ONE DECODE STEP the L2 program,
  and the loop is an induction in the logic. A loop in the logic is not a loop in the machine code, so the compiler still has to
  produce the loop. (a) **DEFLATE FIRST, with a generic verified DRIVER.** One machine-level theorem, independent of the program
  and proved once, says: if the compiled step refines the L2 step relation, then a fixed driver loop (call the step, test its exit
  code, jump back) refines the iterate. That is the "lowering theorem that composes step lowerings" which X1 names, and it is the
  n-call generalisation of `two_emits_same_sender`. (b) **L1′ FIRST:** a new layer object (L2′) in which `inflate` is one term with a
  real loop that holds its capabilities, compiled directly. That means a pin, both arms, and a sitting, all before DEFLATE starts.
  **Rec (a).** No language change. The driver theorem is needed for any step-shaped program, the router included, and DEFLATE is not
  delayed. L1′ stays NAMED and OWED: it is triggered by the first program whose loop cannot be put in step form (state that does
  not fit one cursor record, or nested loops that hold different capabilities). Default (a).
- **C1 — the form of the guarantee.** (a) a VERIFIED compiler: one ∀-program theorem per stage. (b) TRANSLATION VALIDATION: an
  untrusted compiler, with a checker run on each output (A.4's per-program proof, mechanised). **Rec (a)** for the restricted
  source of C2, because L2's grammar is small (the Lean L2 arm is ~3,050 lines across 24 files) and a ∀ theorem is the claim his
  step 1 asks for. (b) is the declared FALLBACK for any one stage whose ∀ proof goes past its price at the checkpoint in §4. If it
  is used, it is recorded per stage and never in silence. Default (a).
- **C2 — the source fragment.** (a) FIRST-ORDER L2: functions only at top level, no closures that escape, and `fix` only as a
  named top-level function. That matches OBJECT-L3 (R-b) (a λ/fix body is checked with Δ = ∅). A program outside the fragment
  is REJECTED by a checked syntactic predicate and is never miscompiled. (b) full L2 with closure conversion and heap-allocated
  environments. **Rec (a)**: the router and DEFLATE's step both fall inside (a), and (b) adds a heap allocator to the trusted
  runtime with no program asking for it. Default (a).
- **C3 — where the instruction library lives.** (a) a PUBLIC shared library in x86lean (effect equations plus the block-simulation
  interface), which paris builds as x86lean work, generalised from Router/Steps. (b) private inside vir. **Rec (a)**: it is
  x86lean's proof interface (ruling ⑧: *"a twenty-instruction routine provable in tens of lines"*), the x86 saltbench lane needs the
  same thing, and the provenance law already covers it. Default (a). It needs paris's lead and the helm's routing, not a word from him.

## 3. What x86lean has to supply, and what paris owes
- **Semantics:** user-level 64-bit integer `stepP` only, with no FP, no SIMD and no syscalls. The output's I/O is memory regions
  that the caller sets up, as in the router's buffers. Instructions: mov (reg/mem/imm, sizes 8 and 64), movzx byte loads, lea,
  add/sub/and/or/xor/shl/shr, cmp/test, jcc/jmp, call/ret. Every one has to be on x86lean's differential-validated list, and the
  plan lists which ones at the pin.
- **paris owes (C3 (a)):** (1) effect equations for that set, in the `{ s with … }` form; (2) a straight-line-block lemma with a
  conditional exit over `stepP`; (3) call/ret under ONE internal calling convention (SysV at the entry point only); (4) the driver
  theorem of C0 (a), or its machine half, with vir proving the L2 half.

## 4. Size and cost, as an ESTIMATE (not a measurement)
The basis is the arms' own logs. The Lean L2 arm was 79 builds in one day (three heads, 11-03). The L4 arm was 109 builds in one day
(four heads, 11-06). The router spike, A.4 for one program, took paris several heads.
**Guess:** S1 ~40 builds / 1–2 vir heads · S2 ~40 / 1–2 · S3 ~60 / 2–3, plus paris's library work (2–3 heads) · S4's test pipeline
1 head · the driver theorem ~30 / 1. **Total ≈ 170 builds, 6–9 vir heads and 3–4 paris heads. Sittings: 2** (this plan's forks,
then the results). **CHECKPOINT:** after S1, the S1 figure is set against its 40-build guess. Over 2× means C1's fallback is
considered for S2/S3 and posted before it is taken. The DEFLATE step through the compiler comes after DEFLATE's own L2 proof and
is not counted here.

## 5. What this plan does NOT claim
no optimisation · no register allocation beyond a fixed spill-everything scheme · no L4 (`par`, locks) and no concurrency · no
claim about the bytes beyond XED's decode and a differential run · no MetaPRL arm for the compiler (MetaPRL's queue: Y5 to the 11-08
cap, SLang, L3, L4) · no performance figure · no real loader or OS ABI past the SysV entry · no claim that the "spill everything"
code is what a production compiler would emit.
**What would show this plan wrong:** a stage's theorem stated after its proof · a program accepted outside C2's predicate · the
fault exit reached on a run the L2 semantics does not fault on · the driver theorem quietly specialised to one program.
