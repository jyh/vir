# X5 run 1 — Appendix S (the Lean arm's executable spec) against zlib 1.4 raw inflate (2026-11-11 14:15, the 62nd vir head)

Pinned before the run at vir e33de77 (DECLARATIONS-DEFLATE.md, Addendum A2). The oracle is zlib 1.4 (tarball sha256 02dd1597…).
The arm is `inflateLit` and `inflate` from `VIRDeflate/Spec.lean` at that commit, built at df-008 (`saltbuild EXIT=0`).
Produced by `python3 x5/run_x5.py <zinflate> .lake/build/bin/x5 <work> x5/X5-RUN-1.tsv`, rc 0. Rows: `X5-RUN-1.tsv`. Printed
summary: `X5-RUN-1.summary.txt`. Inputs were hash-checked against both manifests, and `gen_corpus.py --check` and
`gen_addendum.py --check` returned rc 0 inside the run.

## The result
| reading | AGREE | VERDICT disagrees | BYTES disagree |
|---|---|---|---|
| `inflateLit` (S read literally; **D1 is scored here**) | 266 | **47** | 0 |
| `inflate` (DEFLATE-E1's repaired reading) | **313** | 0 | 0 |

The oracle gave 232 ACCEPT and 81 REJECT.

**All 47 disagreements are E1 and nothing else.** In each, zlib gives ACCEPT and `inflateLit` gives REJECT "incomplete", and in
all 47 the stream's first block is BTYPE 01 (fixed). Under `inflate` every one of them agrees, bytes included.

## amend-23 D1, scored
- **ACCEPT/REJECT: FALSIFIED.** "0 errata against S on accept/reject" fails: 47 disagreements are traced to S's text (S5's
  FIXED_D under S4's `code`). The erratum was recorded BEFORE the spec was built, by reading. The run measures it, and the
  count is the run's.
- **REASON: HOLDS.** "≥ 1 reason disagreement" is met by the predicted pair, S's *"repeat with no first length"* against zlib's
  *"invalid bit length repeat"*, on exactly one input. That input is Addendum A1's `iiia1-repeat-no-first`. The pinned
  `iii-repeat-no-first` never reaches the clause (STAGE-DEFLATE finding 2), so **without A1 this half would have had no input to
  fire on.**

## Reasons on double REJECT (`inflate` against zlib; reported, never scored, S8)
- 53 truncations are zlib's `Z_BUF_ERROR` (no message) against S's "truncated".
- The others pair one to one by meaning. The table is in `X5-RUN-1.summary.txt`.
- One pair is worth naming: zlib's "invalid distance code" against S's "invalid code", on a fixed block reading distance code
  30 or 31.
  - S5's comment says S rejects such a read with "invalid distance code". That presumes FIXED_D HAS codes for 30 and 31.
  - S5's own lens list gives it 30 symbols, so `decode` finds no code and S4 says "invalid code".
  - It is the same 30-vs-32 seam as E1, at the level of a REASON. It costs no verdict, and it is noted, not entered as an erratum.

## Declared, against my own pin
- **The population is 313, not the "313 + 1 = 314" Addendum A2 says.** The 313 pinned FILES include `ii-seed-raw`, the
  uncompressed seed text, which is not a stream (class `seed`). So the pinned STREAMS number 312, and with A1 the population is
  313. The run is right and the declaration's arithmetic was wrong. A correction line is appended to the declarations, and the
  addendum's text is left as written.
- **One smoke run of the oracle** (`i-fixed-one-literal` → ACCEPT "a") was taken after A2's text was written and BEFORE A2 was
  committed. It is the only oracle output that preceded the pin's commit.
- **The positive control is weak in its choice of input.** It altered the first double-ACCEPT, which is
  `i-stored-empty-final`, whose output is EMPTY. So it compared empty against one byte. It fired (BYTES), which proves the
  byte comparison is reached, but a non-empty output would be a stronger plant. A second run would choose a non-empty one.
- X6: no input reached OUTMAX (2^26). No overflow REJECT appears in either reading.
