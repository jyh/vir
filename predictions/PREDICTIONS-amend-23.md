# PREDICTIONS amendment 23 — OBJECT-DEFLATE (the first application) and OBJECT-COMPILER (the VIR → x86-64 compiler)

Written 2026-11-11 by the 61st vir head and pinned in the same commit as `object-DEFLATE/` and `object-COMPILER/`, **before
any DEFLATE file and before any compiler file**. Both objects were ruled at their recommendations at the 11-11 council (his word
*"yes accept"*). OBJECT-DEFLATE names amend-23 as its predictions file. This file also carries the compiler's predictions, as
the compiler plan's own rule requires ("written after his yes and before the first compiler file").

**What was known when this was written.** The census below runs over every ref of this repository and of x86lean at origin/master 5f2231f.
- This repository, `.lean` files: `git log --all -S` reads **0** commits for `Huffman`, `inflate`, `BlockIR`, `overflowExit`
  and `stepP` (control `Y5` = 10).
- x86lean: **0** for `Huffman`, `BlockSim` and `blockSim` (control `stepP` = 32). Its 18 `inflate` hits are English prose ("inflate a
  figure"), read at `git grep -l`.
- L1/L2 as built: `int` is `Int`, and P = {add, sub, mul, lt, le, eq, and, or, not, max}. Both are read in this commit's
  declarations, so no row below can claim to be blind to them.
- The MetaPRL arm builds neither object: X0 (a) for DEFLATE, and the plan's §5 for the compiler. The rows are therefore Lean-only,
  with ONE arm. They measure the method against its own estimates, not one logic against the other.
- The writer of this file is also the builder of both arms. That was true of every Lean-arm row since amend-1 and is said again
  here. The defence is the same: a row is a count or a verdict that the harness reads from artifacts, and it is fixed before the
  first file.

**The 11-06 rule binds here too.** Past ~100 tactic applications in one proof, the arm stops and systematizes, and
tactic-building time is a separate ledger line.

## §D — DEFLATE (Lean arm; the object's §2 rows, at X0–X6 (a))

| id | prediction | measured by | falsified if |
|---|---|---|---|
| D1 | Appendix S, transcribed as the arm's executable spec, AGREES with zlib raw inflate on ACCEPT/REJECT for every input of the X5 corpus, so **0 errata against S on accept/reject**. On REASON it disagrees on **≥ 1** rejected input: S's *"repeat with no first length"* is zlib's *"invalid bit length repeat"*. | the X5 run's log at a pinned corpus hash; `errata/ERRATA-DEFLATE.md` | any accept/reject disagreement traced to S's text rather than to the arm's transcription |
| D2 | DEFLATE needs **no change to L1 or L2**: 0 files under `l1/` or `l2/` touched by a DEFLATE commit, and 0 L2 errata caused by DEFLATE. | `git log` over the DEFLATE commits; `errata/` | either count > 0 |
| D3 | **The input cursor alone is NOT a termination measure.** Under X1 (a) and OBJECT-L3 (R-b), no L2 term that holds the output capability can loop, so a back-reference copy, a stored copy and a code-table build each advance by ONE cell per step, and those steps consume no input bit. The proved measure involves the output side (OUTMAX − m, or a pending count bounded by OUTMAX under X6). | the termination theorem's statement at its sha | the arm proves termination with a measure that is a function of the input bit position only |
| D4 | Bit extraction uses **no new primitive** (P unchanged), through a pure top-level recursion over `Int`. That recursion is ≥ 1 `fix` in the step program. | the program's term; D2's count | P gains an operator, or bits come from something other than L2 terms |
| D5 | The canonical-code part (S4's construction, the Kraft completeness and over-subscription lemmas, decode's uniqueness) is **≥ 25 % of the DEFLATE arm's C5 tokens**. | `count.py`, a DEFLATE arm, by file group declared before the first proof | < 25 % |
| D6 | The DEFLATE arm, from the first file to correctness (X3 (a), both halves), takes **> 109 builds**, more than the largest single-layer day so far (L4's). | `saltbuild EXIT=` lines in the arm's `logs/` | ≤ 109 |
| D7 | Safety on EVERY input (X3 (a) first half: no index fault, and termination) is proved with **no premise on the input bytes**, only on n and OUTMAX. | the safety theorem's statement | a hypothesis on the bytes of b |

## §K — the compiler (Lean; C0–C3 (a), C4 (b))

| id | prediction | measured by | falsified if |
|---|---|---|---|
| K1 | S1 (L2 → block IR, the forward simulation) takes **more than the plan's 40 builds and no more than its 2× checkpoint: 40 < S1 ≤ 80**. | `saltbuild EXIT=` lines over S1's files, from the first S1 file to its simulation theorem's EXIT=0 | ≤ 40, or > 80, which also triggers the plan's checkpoint |
| K2 | **No stage uses C1's translation-validation fallback**: S1, S2 and S3 are each one ∀-program theorem. | the stage theorems' statements | any stage is per-output |
| K3 | **The driver theorem (C0 (a)) names no program**: the constants in its statement are drawn only from the compiler's, L2's and x86lean's namespaces, and none of them belongs to DEFLATE or the router. | a harness check over `#print` of the statement | a program constant in it |
| K4 | **The instruction set the compiler emits is ⊆ §3's list ∪ {`imul`, `setcc`, `jo`}** (the three declared at the pin). | the S3 code generator's instruction constructors | any other mnemonic |
| K5 | Under C4 (b), **the overflow exit is proved UNREACHABLE for DEFLATE's step** whenever n and OUTMAX are < 2³², with no per-input premise. | the theorem at its sha | the bound needs a premise on the input, or the exit is reachable |
| K6 | S2's layout premise (disjointness + bounds) is discharged ONCE from L2's capabilities: **0 per-program layout lemmas** for the router or DEFLATE. | the files named `*Layout*` per program | > 0 |
| K7 | **The router as an L2 term (`inputs/L3-programs.md`, F at NW = 64, NS = 4, NT = 4), compiled by the compiler, reproduces A.4's verdict.** Its five exits are witnessed, as in paris's hand lowering of program 1, and the L3 router triple is carried to the machine with no router-specific lemma. | the composed theorem at its sha | a router-specific lemma is needed, or an exit is not witnessed |

## Declarations owed before the first file
- **DEFLATE:** the C5 file groups for D5 (which files are "canonical code"), and the X5 corpus hash with its generator. Both are
  committed before the arm's first proof file and before the first zlib run.
- **Compiler:** S1's file list (K1's population), and the namespace whitelist for K3. Both are committed before S1's first file.

## Order (the plan's, at its recommendations)
S1 first. It does not wait on DEFLATE, because it is generic over L2 and is checked first on the L3 router term (K7's population). The
DEFLATE spec and X5 run in parallel with S1. paris's library work (C3 (a)) is routed at this pin.
