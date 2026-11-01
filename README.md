# vir — a Verification IR, measured in two logics

vir is a campaign, not a library. It takes ONE frozen object, the appendix of the O94 paper
(*verification agents* and the spec-first method), and mechanises it in two logics, Lean 4 and
MetaPRL's Computational Type Theory. The aim is to MEASURE where each logic pays, rather than argue it.
The predictions of where each arm pays were written and committed before either arm's first proof.

## The frozen object
`object/` holds the paper's appendix A.1–A.4 and its §5 exhibits, byte-exact line ranges of the paper's
source at the build named in `object/MANIFEST.md`, frozen at **60077d3**. Nothing in `object/*.tex` is ever
edited. An erratum is a separate file, `errata/ERRATA.md` (E1–E10).
- A.1 the ontology · A.2 the grammar and four rules · A.3 three rewrites and the fused term (the router)
- A.4 a hand lowering of the fused router to x86-64 assembly

The paper itself is not yet posted. Its appendix text is public here first, deliberately.

## The preregistered predictions
`predictions/PREDICTIONS.md`, committed at **520cd76** before any proof existed in either arm. Its first lines
say so. The five predictions are:
- **P1:** Lean pays transport casts at `slice_fuse`.
- **P1b:** that cost is a representation choice.
- **P2:** CTT pays in well-formedness obligations.
- **P3:** the object under-states its rules.
- **P4:** the trusted base is equal.
- **P5:** A.4 as written is not a refinement.

The counts that score them (C1–C6) are defined in the same file. Every later change is a new dated file,
`PREDICTIONS-amend-<n>.md`, which states which proofs it was written after. amend-1 is at 04447e3 and
amend-2 at 032fcbb, both before any proof. Programs 2 and 3 were pinned before their own proofs: Q1–Q5 at
a7cf800, T1–T5 at f088663. The first Lean proof is dd642ca.

## The arms
- **Lean** (`lean/`, this repo): shallow and deep embeddings, indexed (L-IDX) and flat (L-FLAT) slices.
  Every build ran through one wrapper and is judged only by its `EXIT=` line. `lean/out/` holds the
  `#print` terms and `#print axioms` output the counts are read from.
- **MetaPRL** (the `mojave/vir-arm` branch of `github.com/jyh/metaprl`, pushed after this repository): the same three programs in CTT.
- **The compiler spike** (a branch of `github.com/jyh/x86lean`, pushed after this repository): A.4 against x86lean's semantics.
  `compose/` joins its refinement theorem to the Lean arm's specification: one theorem from the router's
  meaning to the machine. It pins the spike at adbf22f (branch `spike/o95-router`) and builds through the same
  wrapper (compose/logs/build-024, audit-008: `EXIT=0`).

The two proof arms were built by different agents. Neither read the other's proofs before its own were
committed. For the Lean arm this is recorded in `SUMMARY-first-act.md`, which also says what was not measured.

## Where to start
1. `SUMMARY-first-act.md`: every verdict, with its count, the reading it is scored under and when that
   reading was pinned.
2. `RESULTS-1.md`, `RESULTS-2.md`, `RESULTS-3.md`: the measurements and their addenda.
3. `FINDINGS.md`: what each arm found about the object and about itself.
4. `REVIEW-O95-2026-11.md`: the open questions.

To re-derive every committed count file from the artifacts, run `harness/reproduce.sh <metaprl-root>`.
It extracts counts only and does not rebuild. `harness/selftest.sh` shows that the extractor can fail.

## Limits (each one rides with the verdicts it bounds)
- Three programs, all from one router family, and one proof chain per arm per program.
- Some counting conventions were written after a proof (amend-3, amend-4, amend-6, and the `≍` glyph
  correction in RESULTS-2 §0). Each file says so, and verdicts are reported under both readings where
  the readings differ.
- **FINDINGS X-F1: A.4 never bounds the sender.** The ACL table and the bucket array are indexed by an
  unbounded 32-bit sender, so they span 2^35 and 2^34 bytes. The compiler theorem therefore needs a
  layout at high addresses. This is a property of the frozen object, not of the proof.
- The two-call theorem covers two calls, not n. Between the calls, the caller writes only the second
  call's buffer.
- A.4 *as written* is refuted (P5, errata E2 and E3). The refinement theorem is about A.4 as repaired by
  errata E1–E5.

## In progress
A declared amendment to the typing style of both arms (B → B′) is in progress. In the MetaPRL arm it
adds `prim` well-formedness rules over typed carriers, never `top`. The Lean arm mirrors it with an
abstract carrier, and a parser from A.2's text into the deep embedding adds a transcription check.
The predictions are untouched, and both arms will be re-scored on it.

## History
This repository's history was rewritten once, on 2026-11-01, before its first push. The rewrite removed
session trailers from 10 commit messages and replaced home-directory, scratch and internal-log
references with placeholders (`~/fleet/`, `<scratch>/`, `@[bus]`), including inside committed build logs.
It also dropped one tracked `.pyc`. Nothing else in any file was changed. Author and commit dates are the
originals. Prose in the tree cites pre-rewrite shas, which `PREREGISTRATION-SHA-MAP.tsv` resolves (old sha, new sha, original author date, role, subject; one row per commit).

Licence: Apache-2.0.
