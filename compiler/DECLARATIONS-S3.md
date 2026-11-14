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

## ADDENDUM 1 (2026-11-14, the 76th head, after Frame.lean's `wid` and BEFORE Fragment3.lean): HEAD-RELATIVE ρ, which REVISES S3-F
**A first form of this addendum, never built on, is withdrawn.** It closed ρ's length with ONE parameter and result width per
table, and it claimed "the router's and DEFLATE's tables pass it". Checked the same hour: the router has no `app`, and DEFLATE's
table has three functions (pow2, strip, bit) with parameter widths 2, 4 and 3 (a fix receives its own label). So it would have
REJECTED DEFLATE. The check pointed at a simpler design:
- **ρ grows at the FRONT** (`ws ++ ρ'`, `m(…) :: ρ`, `base :: len :: ρ`), and a `slice off len` counts from the NEWEST word. So
  ρ is laid out with its newest word at the LOWEST address, and a register `envLow` points at it. `ρ[off]` is `[envLow + 8·off]`.
  A prepend of n words is `envLow −= 8n` plus the stores. **No slot address depends on ρ's length**, so S3-F's static length, its
  frame bound and a width discipline are all unnecessary. S3-F (a) is REVISED to this: the frame is the downward-growing env
  region, addressed off `envLow`.
- **`letE`** saves `envLow` (it is the continuation's ρ) and calls c₁. **`ret o`** writes its `wid o` words to the result area
  and the count to a register, and returns. The continuation restores `envLow` from the saved slot and prepends that many words.
  The count is a RUNTIME value, so a callee's result width is never needed statically.
- **`app f x`**: x's words go to the result area, `envLow` is reset to the current ACTIVATION BASE (the `envLow` the innermost
  pending `letE` saved, or the entry value), and the words are prepended, plus the label for a fix. A tail call therefore reuses its
  activation's space. A loop of tail calls runs in constant stack.
- **S3-S's RES clause, restated on the word state:** RES is reached only when the word state's size exceeds the declared stack
  region. The size is `|ρ| + Σ over k of (|ρᵢ| + c)`, with c the constant per continuation (the saved `envLow` and the return
  address). This is a measure of the state, not a premise on the run.
- **`Fragment3.ok`** checks only encodings: offsets fit the displacement form, and the table size fits the dispatch chain. It
  checks no widths. A BAD shape (S2's `none`, which no compiled typed program produces) has no x86 counterpart claimed: S3
  simulates the word steps that exist.

## ADDENDUM 2 (2026-11-14, the 77th head, BEFORE S3/Lower3.lean): the machine convention, written out
Addendum 1 left three things unstated. Each is fixed here before any code that depends on it. Each has a recommendation, and the seat
proceeds on it.
- **S3-E, instruction lengths.** x86lean's `Instr` carries its encoded length, and there is no encoder (decode is trusted to XED).
  (a) **The length is a PARAMETER** `ilen : Op → Nat`, with 1 ≤ `ilen` ≤ 15 as the only premise. Every branch uses its fixed-length
  rel32 form: `jcc` 6 bytes, `jmp`/`call` 5, `ret` 1. So no length depends on a displacement, and a sub-term's code size does not
  depend on its address. The theorem quantifies over `ilen`. (b) Model an encoder. **Rec (a)**: an encoder is not S3's subject.
  A later encoder discharges (a) by exhibiting its `ilen`.
- **S3-M, regions (REVISES Addendum 1's single stack region into TWO, plus a buffer and a control block):**
  ENV (ρ's words, growing down, `envLow` in **r12**), the x86 STACK (`rsp`: per pending `letE`, the saved `envLow` and the return
  address, 16 bytes), BUF (the operand buffer and result area of S3-R in one region; base in **r14**), and CB (a control block; base in
  **rbx**: `[rbx]` STATUS, `[rbx+8]` the saved driver `rsp`, `[rbx+16]` ENV's low bound, `[rbx+24]` STACK's low bound). The result
  COUNT travels in **r13**. Temporaries are rax, rcx and rdx. All four regions are pairwise Apart, Apart from every live L2 region, and
  do not wrap.
- **S3-L, the code shape.** Code for a sub-term is generated at a known address with every sub-term's code placed CONTIGUOUSLY (an
  out-of-line `letE` body sits after its continuation's code, which never falls through). Operands are evaluated into BUF at a static
  slot: `slice` copies from `[r12 + 8(off+j)]`; `arith` evaluates `a` at slot t and `b` at t+1, then add/sub/imul + `jo OVF`, or
  `cmp` + `setcc` into a zeroed rcx (lt/le/eq), or `cmp` + `cmovle` (max), or and/or; `bnot` is `1 − x` by `sub`; `cat` places `b` at
  t + `wid a`; `drop` moves words down; `tag` writes the tag at t and the padding after `a`. BUF's static need is `need o`, a function
  of the operand, which `Fragment3.ok` bounds.
  `letE c₁ c₂`: a STACK check, `push r12`, `call c₁`, `pop r12`, then a LOOP prepends r13 words from BUF to ENV (the only loop in a
  step: the count is a runtime value by Addendum 1). `ret o`: o into BUF, `r13 := wid o`, `ret`. `app f x`: f into BUF and then rdx,
  x into BUF, `r12 := [rsp + 8]` (the activation base), then a dispatch chain whose entry i prepends x's `wid x` words (plus the
  label for a fix: it is ρ's LAST word) and jumps to body i. The top level enters through a stub that saves `rsp` to `[rbx+8]`,
  pushes r12 and calls the body, so `[rsp + 8]` always exists. FAULT, OVF and RES write STATUS, reload `rsp` from `[rbx+8]` and `ret`
  to the driver. DONE is the stub's `ret` after STATUS := DONE.
- **S3-S restated (REVISES Addendum 1's measure into an UPPER BOUND over two regions).** ρ and the continuation environments SHARE
  ENV words (`letE` gives c₁ the same ρ), so ENV's occupancy depends on the run's history, not only on the word state. What is
  claimed: RES is reached only when `8·(|ρ| + Σ over k of |ρᵢ| + n)` exceeds ENV's size for the n words being prepended, or
  `16·(|k| + 1) + 8` exceeds STACK's. Sharing only lowers occupancy, so this is the true bound's contrapositive and is still a
  measure of the state.
