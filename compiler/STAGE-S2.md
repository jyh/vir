# Compiler S2: layout to 64-bit words, PROVED (2026-11-11, 61st vir head)

**Theorem `VIRC.s2_refines`** (`VIRC/S2.lean`). `#print axioms` gives propext · Classical.choice · Quot.sound
(`logs/s2-audit-001.log`, `saltbuild EXIT=0`). The `sorryAx` control is red (`logs/s2-audit-control-001.log`).

It covers a ⊢₂-typed program accepted by C2 and S2's predicate: closed below its caller context Γ₀, no alloc/free, constants in
range, a code table under 2⁶⁴ entries, caller parameters related (`EnvRel`), and a layout satisfying the premise
(`Layout`, `MemRel`). For such a program:
1. an IR run that FINISHES with v is matched by a word run that finishes with words related to v, or that reaches OVERFLOW;
2. an IR run that is STUCK is matched by a word run that reaches the FAULT exit or the OVERFLOW exit;
3. n IR steps are matched by exactly n word steps, or by an earlier stop at OVERFLOW. The simulation is lock-step.

**On no run does the word machine finish with an unrelated value.**

**Mutant, red, and it tests C4 (b) directly.** `mutants/Word-wrap.lean` removes the range check (`chk` always returns the
wrapped word).
- Built alone, it fails at the concrete check `run_ovf` (`logs/s2-mutant-wrap.log`, EXIT=1).
- Built with that one check removed, so that the build reaches the theorem, it fails in the proof, at `chk_out` in
  `VIRC/Sim2.lean` (`logs/s2-mutant-wrap-thm.log`, EXIT=1).

Both originals were restored, and `s2-041` rebuilt the tree green.

**Builds.** 41 to the first green audit (`s2-001` … `s2-040`, then `s2-audit-001`), against the plan's §4 guess of ~40 for S2.
All `s2-*` logs: 47, adding a probe, three mutant runs, a rebuild and the control. No amend-23 row predicts S2's build count, so
this is a reading, not a score. **K6 HOLDS so far**: no file states a layout lemma about one program.

## Limits (they ride with the verdict)
- **S1 ∘ S2 is STATED and PROVED: `VIRC.compile_refines` (`VIRC/Compose.lean`, `logs/s2c-audit-001.log`, standard axioms).**
  It is ONE statement about the SOURCE program with its caller parameters instantiated (`instL 0 vs e`):
  - a ⟶₂ run that finishes with `ret a`, ⟨a⟩ = w, is matched by a word run finishing with words related to w's image, or by
    OVERFLOW;
  - a ⟶₂ fault is matched by FAULT or OVERFLOW;
  - n ⟶₂ steps are matched by ≥ n word steps, or by OVERFLOW.

  Logs `s2c-*`: 3 builds and 1 audit, beside S2's count.
- **S2's converse is PROVED: `VIRC.s2_converse`** (`logs/s2c-audit-002.log`, standard axioms). If the word machine FINISHES with
  `done ws` from a related start, the IR run finishes with a value related to ws: the word machine's answer is always an IR
  answer. It rests on lock-step (`s2_run`), word determinism (`WN.det_stuck`) and `ir_classify`.
  **Still owed:** the composed converse about the SOURCE (word finishes ⇒ ⟶₂ finishes). It needs `s1_converse` restated from
  `compile_refines`'s initial Match (caller parameters) rather than `match_init`, which assumes a closed program.
- The word memory is word-granular (`W → W` at cell addresses). The byte view (x86lean's `Mem`, 8 bytes per cell) is S3's bridge.
- The code-table bound (< 2⁶⁴ entries) and the layout premise are HYPOTHESES the caller discharges. They are not checked by the
  compiler.
- The fault clause is the corrected one (FAULT or OVERFLOW). See the correction below, written before the theorem.


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

  - part 5, groundwork: `load_sim` (a live cell's load reads its value's word), `bounds_iff` (the word bounds test is L2's),
    `slice2` (a capability's two words), `toInt_ofNat_small`, `ofInt_nonneg`, and `VRel/EnvRel.transport` (the relations read
    σ only through R, which a store keeps).

## A CORRECTION to DECLARATIONS-S2's theorem form, found while specifying the step (written BEFORE the step theorem exists)
The declaration says *"an IR run that is stuck is matched by a word-machine run that reaches the FAULT exit"*. That is too
strong. A load or store whose INDEX computation overflows makes the IR stuck at the out-of-bounds op, or not stuck at all, while
the word machine stops at OVF first. The clause will be stated as **"… reaches the FAULT exit, or the OVERFLOW exit"**. The
declaration's third clause (*OVF only where an int leaves the range*) is what that disjunct means, and **no clause allows a wrong
finished value**. The declaration is left as written, and this is the record of the change.

## The step simulation, as it was specified before it was built (DONE: `sim2_step`, `s2_run`)
- **State relation** `SRel T lay (I : St × Store) (Wst : WSt × WMem)`:
  - `run`: ∃ e Γl Γt Δ τ t with `c = lowerT e`, `wc = (lower2T Γl e t).1`, `KeepsFrom t.length (lower2T Γl e t).2 T`,
    `HasType₂ Γt Δ e τ`, `Tm.wfB Γl.length e`, `Agree Γl.length Γl Γt`, `fnOk e`, `ok2 e` and `EnvRel T lay σ Γl ρ ρw`.
  - Frames: `FRel2 τ k kw τfin`, a chain in which each frame's continuation is the same data at `τin :: Γl`, typed
    `τin :: Γt ⊢ e₂ : τout`.
  - `Layout σ lay` and `MemRel lay σ m`.
  - `done`: `VRel τfin v ws`.
- **Step lemma** (lock-step, one word step per IR step). From related states, an IR step is matched either by one word step to a
  related state, or by one word step to `ovf`. Case by case:
  - ret: pop or done, via `opd_sim`.
  - letE: push both.
  - load: `load_sim` + `bounds_iff` + `slice2`.
  - store: `layout_store` + `memrel_store` + transport; the rebound cap is `VRel.cap`.
  - app: the label's `CodeAt` gives the body's code at `[τ₁]`. `BodyOK` and `Agree 1` re-establish the relation in the body; a
    fix's environment adds the self label's `VRel.fix`.
  - ite and case: from `VRel.bool`, `.inl`, `.inr` (`take (size τ₁)` of the padded words).
- **Stuck lemma**: a stuck IR `run` state under SRel is an out-of-bounds load/store (typed atoms always evaluate: `opd_sim`), and
  the word machine steps to `fault` or `ovf`.
- **S2 theorem**: the four clauses with the correction above. Then compose with `s1_refines`/`s1_converse` into one statement
  about the source term.
