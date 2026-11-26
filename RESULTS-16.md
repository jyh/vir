# RESULTS-16 — the eager entry check for an external caller (OBJECT-NOCHECK-ENTRY, PREDICTIONS-amend-27 NE1–NE8)

Scored 2026-11-25 by the 91st vir head. The object (c346d50) and amend-27 were pinned by the 90th head before any route file. Errata
E1–E3 (`errata/ERRATA-NOCHECK-ENTRY.md`) govern the interface: by E3, the decider has type `tcap` and rejects by a deliberate index
fault, because L2 is linear in capabilities. The writer is also the builder. Every figure below is read from a committed artifact
named in its row. **A non-author read of `compile_entry`'s statement is OWED.** It is asked for on the bus with this file. Until it
lands, this page reports what was built and measured, not a read.

## What was built
- **`S3.compile_entry`** and **`S3.compile_entry_run`** (`s3/S3/Entry.lean`, NE-T). An external caller sits at the loop head H in
  `AtHead` with a capability (p₀, n₀). H holds `call base_d` and Driver3's `loopTail env0 XF H₂`. H₂ holds `call base_e`. The decider d
  is compiled CHECKED (`lower3B true`), and e is compiled UNCHECKED (`lower3u`). The premises are compile_x86's shape premises for both
  programs, d's read-only predicate (`ReadOnlyW`), and d's SOUNDNESS: every finishing run of d leaves σ, returns the capability it
  was given, and gives NC-P′ for e. The conclusion has two parts.
  - (F) Every faulting run of d puts the machine at XF, with every live cell still representing the start memory (`AtFaultX`).
  - (D) Every finishing run of d either does the same (d's OVF or RES), or reaches e's base in `DriverCall`. From there, e's runs are
    matched exactly as `compile_x86_provedS` states them.
  There is no `P σ` premise and no premise that e's run is fault-free at σ.
- **`K7.dF`**, **`K7.dF_sound`** and **`K7.router_entry`** (`k7/K7/RouterEntry.lean`, NE-R).
  - dF reads SvA and TvA by R4's own `RD32` macro. If both lie in [0, 4) it returns its capability. Otherwise it loads index −1.
  - dF_sound proves the soundness premise from R4.
  - router_entry is the router F entered through `compile_entry_run` with no premise on SvA or TvA.
- **`K7.PTriple`** and its rules (same file): `Triple`'s `ret` clause alone, meaning that every FINISHING run ends in Q. dF faults by
  design, and L2's `Triple` promises no fault, so `Triple` cannot state dF's soundness. The rules are:
  - `ptriple_of`, `ppre_pure`, `pletOp_rule`, `ppure_step_rule`, `pite_true`, `pite_false`, `pletRet_rule`: copies of the `ret`
    halves of L2's rules;
  - `pload_neg`: a load at a negative index never steps.

## Scores
| id | prediction | measured | verdict |
|---|---|---|---|
| NE1 | no `P σ` and no `NoFaultP` premise; only shape premises, the read-only predicate, its soundness, e's triple | `s3/probes/NeCheckEntry.lean` (`pp.deepTerms`, log `s3/logs/ne-024.log`, 11,835 B for compile_entry): `Triple` occurs **0** times. `NoFaultP` occurs **once**, as the last conjunct of the decider's soundness premise (`… → σ' = σ ∧ valOf w = cap p₀ ∧ S3.NoFaultP [cap p₀] e σ`), never as a premise about σ itself. compile_entry_run's print (35,360 B) reads the same. | **HELD.** Limit: e's NC-P′ reaches the theorem only through d's soundness, and no triple for e is a premise. The row allowed one, and none was needed. |
| NE2 | names no program | the same print, every `Ns.name` token: the namespaces are S3, VIRC, VIRL1, VIRL2, VIRBridge and X86, plus Lean's BitVec, Finmap and List. `K7.`, `K5.`, `VIRDeflate` and `dF` each occur **0** times. | **HELD.** VIRBridge is the compiler's bridge layer and VIRL1 is L2's base. `harness/ne_counts.py` also lists `L` and `P`: these are the local variables in `L.bufN` and `P.at?`, not namespaces. |
| NE3 | the FAULT outcome states every live cell unchanged, from the read-only predicate | `AtFaultX P L XF m s := ∃ n v, runP P n s = v ∧ ¬stopped ∧ v.rip = XF ∧ Rep m v.mem L.live`. Every reject path gets the word memory `= m` from `readOnly_mem hdro` (Entry.lean, the `reject` helper and its five call sites) and nothing else. | **HELD** |
| NE4 | reuses ≥ 2 of `head_call`, `after_done`, `after_exit`; 0 lines changed in existing `s3/S3` files | `head_call` (twice) and `after_done` are used. The reject path uses `loop_check`, the first half of `after_exit`, because it needs the memory equation that `after_exit` drops. `git diff --numstat 8fc40b8..HEAD -- s3/S3`: new files only (Contain 143, Entry 250, ReadOnly 88), and `s3/S3.lean` +3. | **HELD** |
| NE5 | exactly 1 router lemma beyond the decider's definition | `k7/K7/RouterEntry.lean`: **2** router lemmas (`dF_ptriple`, `dF_sound`), plus **8** generic lemmas and the `PTriple` definition, which a faulting decider needs and L2's logic lacks. | **FALSIFIED.** The cause is E3's interface: a decider that rejects by faulting cannot be stated in a fault-free logic. `dF_ptriple` could have been inlined into `dF_sound`; as built it is a separate lemma, and the count reads it so. |
| NE6 | 15 < builds ≤ 40 to `compile_entry` at EXIT=0 | `saltbuild EXIT=` lines in `s3/logs/ne-*.log`. **19** from ne-001 to ne-019, the first EXIT=0 of E3's `compile_entry`. Router side, not in NE6: `k7/logs/ne-r-*.log` has 11 builds (5 on E2's probe, 2 to `router_entry`, 3 audit-triple builds, 1 count probe). | **HELD at 19, with a disclosure.** E3 extended the population ("continues from ne-018") after 18 builds were known. Read on E2's statement instead, the first sorry-free EXIT=0 was **ne-014**, which gives **14 = FALSIFIED low**. ne-012 carries one `declaration uses sorry` at Entry.lean:192. Whether ne-014's file held the whole E2 `compile_entry` cannot be told from its log. **The non-author read decides which reading is primary.** |
| NE7 | axioms ⊆ {propext, Classical.choice, Quot.sound} | the axiom TRIPLE through logged-build.sh. s3: build ne-020, control ne-021, audit ne-022, `AXIOM-GATE OK rows=103`. k7: ne-r-008/009/010, `AXIOM-GATE OK rows=48`. Both imported controls read `Lean.reduceBool:trustCompiler`. compile_entry, compile_entry_run, compile_x86S, dF_ptriple, dF_sound, router_entry and pload_neg each read `[propext, Classical.choice, Quot.sound]`; readOnly_mem reads `[propext, Quot.sound]`. | **HELD** |
| NE8 | compile_x86's and compile_x86_proved's `#print` byte-identical to 8fc40b8's | `s3/probes/NcCheckDeep.lean` at the tip (log `s3/logs/ne-023.log`) against `s3/probes/nc-*-check-deep.txt`: 6,054 B = 6,054 B and 5,025 B = 5,025 B, **IDENTICAL**. Instrument controls: the same extractor reads ne-018 IDENTICAL, and a one-byte mutant of the capture reads DIFFERS, rc 1. | **HELD** |

**Directions (amend-27, reported only).** Read by `k7/probes/NeCount.lean` (`k7/logs/ne-r-011.log`), with NC2's instrument.
- dF's checked lowering is **386** instructions and its unchecked lowering is **350**. dF has 9 load sites and 0 table functions, and
  36 = 4 × 9, as NC2 predicts.
- So the eager check costs 386 static instructions. Removing the lazy checks from F saved 80 (731 → 651).
- dF has to run CHECKED, because its reject IS the index check firing at index −1. The amend-27 question, whether dF could run
  unchecked, is answered no for E3's form.

## The findings
1. **E3 (the 90th head):** a decider of type `cap × bool` is untypeable in L2. E2's `compile_entry` (55962a3) was proved for an
   interface no program instantiates. It was removed here, and 55962a3 is its record.
2. **NE5 FALSIFIED:** a reject-by-fault decider moves the soundness proof out of L2's program logic. `PTriple` is the smallest
   addition that states it: Triple's `ret` clause, with rules copied from Triple's. It is generic, but no layer below owns it.

## What this does NOT claim
- no check of the SHAPE premises: a malformed store stays outside compile_x86's theorem, as before;
- no speed figure, since 386 and 350 are static counts;
- no decider synthesised from a triple: dF and its soundness are written per program;
- `compile_x86`, `compile_x86_proved`, `lower3` and `lower3u` are unchanged (NE8);
- `k7/probes/RouterEntryCapBool.lean` (E3's record) no longer builds against the tip, because it cites the removed `S3.gateTail`.
