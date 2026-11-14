# Compiler S3, the declarations (word code → x86lean `Program` over `stepP`; OBJECT-COMPILER §1 S3, C3 (a))

Written 2026-11-14 by the 76th vir head, BEFORE any S3 `.lean` file and after paris's C3 (a) landed at x86lean
**paris/c3-effects 4f08f91**: `X86/Effects.lean`, read there by `git show`, never from a working tree. Its names are final
(paris @[bus] 11-14 08:56):
- effects: `stepP_of_at`, `step_add_reg_op`, `step_test_reg_op`, `step_setcc_reg/_mem`, `step_imulr(_of)`;
- blocks: `BlockFetches`, `runBlock`, `runP_block`, `runP_block_then`, `runP_block_jcc`;
- calls: `call_ret`;
- the driver: `driver_iteration`, with `Spec.loop` unchanged.
vir's half already exists: bridge/ (`Rep`, `Apart`, `Sep`, B-3, B-4, `cell_bytes`; DECLARATIONS-S3-bridge.md). The source of S3 is
S2's word machine (VIRC/Word.lean: `WCode`, `WOpd`, `WSt` with environment ρ and continuation stack k, a function `Table`, and
the exits FAULT and OVF). Each fork below is posted with its recommendation, and the seat proceeds on the recommendation (the
08/31 law).

## The forks
- **S3-F, where ρ lives.** (a) **A STACK FRAME per function activation.** ρ's slots sit at static offsets below the frame base
  (slot i at `rbp − 8(i+1)`). `WOpd.slice off len` reads fixed offsets, and the frame size is a static bound computed by one pass
  over the body. (b) Registers plus spills. **Rec (a)**: S2 already made every offset static, and (a) needs only mov to and from
  `[rbp − c]`. Register allocation is an optimisation and is not in S3.
- **S3-K, the continuation stack k.** (a) **x86 call/ret.** `letE c₁ c₂` is `call L₁; <c₂'s code>`, where c₁ runs in the CALLER's
  frame and reads ρ. `app f x` is a TAIL CALL: it sets up a NEW frame for the callee with x as its ρ and jumps. `ret o` returns to
  the innermost pending `letE`. This is `call_ret`'s shape exactly. (b) An explicit continuation stack in memory with an
  interpreter-style dispatcher. **Rec (a).**
- **S3-R, how results come back.** A result is `List W`, whose length is static (the type's flattened size) but unbounded in
  general. (a) **A RESULT AREA**: a caller-supplied region of declared size, the max result size over the program. `ret o` writes
  there, and the continuation copies into its ρ slots. (b) rax/rdx for small results plus memory for the rest. **Rec (a)**: one
  convention, no size cases. The area is one more region in the layout premise, Apart from the rest.
- **S3-X, exits.** (a) **FAULT and OVF are labels** that write a status word to a STATUS cell (a caller-supplied cell) and return
  to the driver by restoring `rsp` from a saved slot, then `ret`. DONE is the top-level `ret` with STATUS = DONE. (b) `hlt` or
  `stopped`, which leaves the driver no exit code to test. **Rec (a)**: C0 (a)'s driver tests an exit code.
- **S3-S, stack exhaustion (NEW at S3; S2's word machine has unbounded k).** (a) **A THIRD EXIT, RES**: each frame setup checks
  `rsp − size ≥ stack_lo` and jumps to RES otherwise. The theorem gains one clause: RES is reached ONLY when the run's
  continuation depth times its frame bound exceeds the declared stack region. (b) Fold it into OVF, which would break S2's OVF
  clause ("only where an IR step would compute an int outside the range"). (c) Assume a large enough stack as a premise on each
  run, which is a premise on dynamic behaviour rather than on placement. **Rec (a).** Answering paris's C3 (3) (STATUS-vir row 330):
  the stack is ONE region of declared size in the layout premise, Apart from every live region, the result area and the status
  cell. `call_ret`'s "slot intact" hypothesis is discharged from that Apart by bridge B-3 (2). No program lemma is involved.
- **S3-D, `app f x`'s target.** In C2's first-order fragment, f is a code label word, an index into the Table. (a) **A DISPATCH
  CHAIN**: compare the label against each table entry and `je` to it. It uses only instructions on x86lean's validated list.
  (b) An indirect `jmp` through a jump table, which needs an indirect-branch form and its validation. **Rec (a)**, with (b) NAMED
  as an optimisation. The chain's length is the table's size, a static constant.
- **S3-I, instruction selection** (no fork, stated so that a count can be read against it). `imm` → `mov r, imm64`.
  `arith add/sub/mul` → `add`/`sub`/`imul` with `jo OVF` (`step_imulr_of`: OF = CF = overflow). `lt/le/eq` → `cmp` + `setcc` +
  `movzx`. `band/bor/bnot` → and/or/xor on 0/1 words. `cat/take/drop/tag` are static rearrangements: word moves between frame
  slots, with no runtime cost model claimed. `load`/`store` → a bounds check (`0 ≤ idx < len`, two compares, `jcc FAULT`), the
  address `base + 8·idx` (`lea`), and a mov of 8 bytes. `ite`/`case` → `test`/`cmp` + `jcc`.

## The theorem's form (one ∀-program statement, K2's form)
For every program that S1's `Fragment.ok`, S2's `Fragment2.ok` and S3's predicate (`Fragment3.ok`: the frame bounds and the table
size fit the encodings) ACCEPT, under S2's layout premise extended by the stack region, the result area and the status cell, all
pairwise Apart and none wrapping past 2⁶⁴:
- a word run (S2) that reaches `done ws` is matched by a `stepP` run that returns to the driver with STATUS = DONE, the result
  area holding `ws` (bridge `Rep`), and every region's cells related by `Rep`;
- `fault` is matched by STATUS = FAULT, and `ovf` by STATUS = OVF;
- STATUS = RES occurs only under S3-S's depth condition;
- divergence is kept (at least one `stepP` step per word step).
Composed with S1 ∘ S2 (`compile_refines`), this carries an L2 triple to the machine. With C3's `driver_iteration` and vir's
`driver_l2`, it carries DEFLATE's iterate.

## Files (planned; a renamed or added file is declared here before it is scored)
A NEW lake project `s3/` beside `bridge/`, so that compiler's and bridge's counts stay put. It requires x86lean BY GIT at
**4f08f91**, re-pinned by EDIT to the merge sha when paris's C3 PR lands, and never pointed at a working tree. It requires
compiler and bridge by path. Packages are APFS-cloned, the manifest is written by edit, the toolchain check comes first (as B-5),
and the logs are `s3-NNN` through its own logged-build.sh.
`S3/Frame.lean` (frame bounds, the slot map) · `S3/Lower3.lean` (WCode → `List Instr` at addresses) · `S3/Fragment3.lean` ·
`S3/Rel3.lean` (the word-state ↔ Cpu relation, built on bridge `Rep`) · `S3/Sim3.lean` (one word step ↔ a block, by C3's block
and call lemmas) · `S3/S3.lean` (`s3_refines`).

## What would show S3 wrong (findings, never routed round)
- a lemma about ONE program (K6/K7's spirit);
- a premise on stored VALUES, or on a run's dynamic depth outside S3-S's RES clause;
- a C3 lemma re-proved inside s3/ instead of cited;
- an instruction used that is not on x86lean's validated list;
- the stack region's disjointness assumed per call rather than discharged once from the layout.
