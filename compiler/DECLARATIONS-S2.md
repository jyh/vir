# Compiler S2, the declarations (layout: values → 64-bit words, regions → address ranges; C4 (b))

Written 2026-11-11 by the 61st vir head, after S1 closed in both directions (`STAGE-S1.md`) and BEFORE any S2 `.lean` file.
Logs are `s2-*` (builds, audits, mutants). A renamed or added file is declared here before it is scored.

## Three forks the plan's §1 leaves implicit, each with the arm taken (the 08/31 law: posted, then proceeded on)
The plan says only *"regions become address ranges, values become 64-bit words and byte cells"*. Three questions sit under that
sentence.
- **S2-R, compound values (pairs, sums, closures-as-code).** S1 erased types, so a pair has no size in the IR.
  - (a) TYPE-DIRECTED FLATTENING. S2 reads ⊢₂'s derivation, so it accepts TYPED programs only. A value of type τ occupies
    `size τ` words: base = 1 (cap: 2, see S2-C), arrow = 1 (a code label), τ₁ × τ₂ = sum of the sizes, τ₁ + τ₂ = 1 tag word
    + the max of the sizes. No heap.
  - (b) BOXED: pairs and sums on a heap, which needs an allocator and either a GC or an unbounded leak.
  - (c) WORDS ONLY: reject every program with a pair or sum value. That rejects DEFLATE's cursor record.
  - **TAKEN (a).** (b) is the runtime C2 (a) exists to avoid, and (c) rejects the first program. The cost: S2's theorem is for
    ⊢₂-typed programs. S1's theorem stays untyped.
- **S2-A, `alloc`/`free`.** (a) S2 accepts programs with NO `alloc`/`free`. Every region is supplied by the CALLER (the plan's
  §3: *"the output's I/O is memory regions that the caller sets up"*) and enters as a capability parameter. (b) a bump allocator
  in a caller-supplied arena. **TAKEN (a)**, with (b) NAMED and OWED. Its trigger is the first program that allocates. The
  router and DEFLATE's step take their regions as parameters.
- **S2-M, cells.** An L2 cell holds an `Int`. (a) ONE CELL = ONE 8-BYTE LITTLE-ENDIAN WORD. (b) byte cells (one byte per cell),
  with a typing or range premise that every stored value is in [0, 256). **TAKEN (a).** It is uniform and needs no per-program
  premise. The plan's "byte cells" is an OPTIMISATION, and it is not in S2. This is a declared narrowing of the plan's sentence.
- **S2-C, a capability value** is TWO words: the region's base address and its length in cells. Bounds checks then need no
  table.

## C4 (b) at S2 (ruled at the pin)
`add`/`sub`/`mul` on `int` are CHECKED. A result outside [−2⁶³, 2⁶³) jumps to the OVERFLOW exit, which is distinct from the FAULT
exit. Constants outside that range are REJECTED at compile time by the S2 predicate (`Fragment2.ok`), never wrapped. A stored cell
is always a word, because only words reach a store. Initial cell contents must fit (the layout premise).

## The theorem's form
For every program that `Fragment.ok` (C2) and `Fragment2.ok` (S2-A, constants in range) ACCEPT, that is ⊢₂-typed with the
caller's parameters as typed capabilities, and for every LAYOUT (regions pairwise disjoint, each inside the 64-bit address
space, every initial cell in range):
- an IR run (S1) that finishes is matched by a word-machine run that finishes with the flattened value, and with a memory
  that agrees with the IR store on every cell of every region;
- an IR run that is stuck is matched by a word-machine run that reaches the FAULT exit;
- the word machine reaches the OVERFLOW exit only where an IR step would compute an int outside the range. **On no run does
  it produce a different finished value.**
- divergence is kept (≥ 1 word step per IR step).

## Files (planned)
- `VIRC/Word.lean`: the word machine. Its registers are a stack of 64-bit word frames, its memory is x86lean-shaped (`BitVec 64`
  addresses, byte memory, 8-byte cells), and it has the two exits.
- `VIRC/Flatten.lean`: `size τ`, and flattening an L2 value at type τ into words.
- `VIRC/Fragment2.lean`: the S2 predicate.
- `VIRC/Layout.lean`: the layout premise and its reading of the L2 store.
- `VIRC/Lower2.lean`: IR → word code, using the typing derivation's types.
- `VIRC/Sim2.lean`: the simulation.
- `VIRC/S2.lean`: `s2_refines`.

## K6's population
K6 holds if no file under `compiler/` states a layout lemma about ONE program. The router's and DEFLATE's layouts are instances
of `Layout.lean`'s premise, discharged by the caller's setup.

## Added before the file exists (same day)
- `VIRC/Infer.lean`: syntax-directed type inference for L2 (`inferA`, `inferT`; no masks), and the theorem that a ⊢₂ derivation
  fixes it: `HasType₂ Γ Δ e τ → inferT Γ e = some τ`. S2 needs the type at every binder, and S1's IR erased types.
- **S2's lowering is indexed by the SOURCE term**, as `lowerT` is: `lower2 Γ e`, with `Γ` the inferred context. The simulation
  relates an IR state (S1's image of e) to a word state (S2's image of the same e). So S1 ∘ S2 is a statement about e, with no
  type re-inference over erased code.
- `VIRC/Table.lean` (added before it exists): the table lemmas. Lowering only APPENDS, or SETS its own reserved slot, so every
  entry below the incoming table's length is unchanged, and the table only grows.
- `VIRC/Compose.lean` (added before it exists, after S2 closed): S1 ∘ S2 as ONE statement about the SOURCE program. The source
  term is the program with its caller parameters instantiated (`instL`); S1's simulation starts from an environment of those
  parameters (`TRel.inst`, by `TRel.subst` outermost-first). Its logs are `s2c-*`, beside S2's count and not in it.
