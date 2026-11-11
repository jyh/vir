# Compiler S2: layout to 64-bit words, IN PROGRESS (2026-11-11, 61st vir head)

Forks are ruled in `DECLARATIONS-S2.md`: S2-R (a) typed flattening, S2-A (a) caller regions, S2-M (a) 8-byte cells, S2-C two-word
caps, and C4 (b), checked arithmetic with an overflow exit.

## Built (green)
- `VIRC/Infer.lean`: type inference. `inferT_sound`: a ⊢₂ derivation fixes it.
- `VIRC/Word.lean`: the word machine. Its environment is one flat word list, memory is word-granular, and there are three
  endings: `done` · `fault` (index out of bounds) · `ovf` (C4 (b)).
- `VIRC/Flatten.lean`: `size`, `offset` and `varSlice`.
- `VIRC/Fragment2.lean`: the S2 predicate, decided by evaluation. `rejects_alloc` and `rejects_big_const` show it rejecting.
- `VIRC/Lower2.lean`: the type-directed lowering. Each λ/fix label is reserved before its body is compiled.
- **Concrete runs, kernel-checked by `decide`** (EVALUATION CHECKS, NOT THE THEOREM):
  - `run_pair`: `let x = 3+4 in (x, 2x)` gives [7, 14].
  - `run_call`: a call through the code table gives [6].
  - `run_case` gives [1].
  - `run_ovf`: 2⁶²·2 reaches the OVERFLOW exit.
  - `run_fault`: load at index 3 of a 2-cell region reaches the FAULT exit.
  - `run_load` gives [42].
  - Red control: `mutants/RunWrong.lean`, the same run expecting [7, 15], `saltbuild EXIT=1` (`logs/s2-mutant-runwrong.log`).

## Built since
- `VIRC/Layout.lean`: the premise (`Layout`), `MemRel`, `cellAddr_toNat`, and `cellAddr_inj` (two live cells share an address
  only if they are the same cell).
- `Lower2`: λ/fix bodies now compile under their own closed context, so a body's code is independent of where its atom
  occurs. The offsets agree either way for a closed body; the change serves the code-value relation.
- `VIRC/Table.lean`: `Keeps`. Lowering only appends or fills its own reserved slot, so every entry below the incoming length is
  final (`lower2T_keeps`). `letOp` now lowers its operands and continuation uniformly, and `opCode` picks the instruction, so
  the table threads one way in every case.
- `VIRC/Sim2.lean`:
  - part 1, AGREEMENT: inference and lowering agree under contexts that agree below a term's bound.
  - part 2, the relations: `VRel` (by type; a code value relates to a label whose final-table entry `CodeAt` is the lowering of
    the same body), `EnvRel`, and `EnvRel.lookup` (a variable's slice reads its value's words).
  - part 3, THE OPERAND LEMMA `opd_sim`/`opdL_sim`: a typed, accepted atom under related environments evaluates in the IR to a
    value of its type, and its word code either OVERFLOWS or yields related words. All ten primitives are covered (checked
    add/sub/mul; comparisons; `eq` through `ofInt` injectivity on the range; `max`; boolean and/or/not), as are λ/fix (their
    labels, against the final table) and pairs, projections and sums.
  - part 4, MEMORY: `layout_store` and `memrel_store`. A store preserves the layout premise and the memory relation, through
    `cellAddr_inj` and L2's own region disjointness (`cell_ne`). R never changes.

## OWED (in order)
1. (was: `VIRC/Layout.lean`, now built): the layout premise. It is a map `lay : Int → W` from region base to address, with regions pairwise
   disjoint as word ranges, no wraparound, lengths < 2⁶³, and `Store.WF`. `MemRel lay σ m` holds when every live cell (p+i) has
   its value in range at `cellAddr (lay p) i`. The cap value `⟨p⟩` corresponds to `[lay p, R(p)]`.
2. `VIRC/Sim2.lean`, the rest (the operand lemma is DONE, above):
   - `VRel tbl τ v ws`: an IR value at type τ against words. A code value relates to a label whose table entry is `lower2T` of
     the SAME source body. This is a relation and needs no decidable equality on code.
   - The table lemma: entries are final once written (reserve, then set).
   - The operand lemma: `evalW` of `lower2A` agrees with `Opd.eval` through `VRel`, or gives `ovf` exactly where an int leaves
     the range.
   - The store lemma: `Function.update` at one cell address preserves `MemRel`. This is the BitVec address-disjointness work.
3. `VIRC/S2.lean`: `s2_refines`, the four clauses in `DECLARATIONS-S2.md`, and its composition with `s1_refines`/`s1_converse`.
