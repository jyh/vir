# PREDICTIONS amendment 28 — the MetaPRL compiler arm (option (iii), ruled at the 11-25 council, Q-7)

Written 2026-11-25 by the 91st vir head, **after the arm's stage X and X′ and BEFORE its S1** (mojave posted at 21:25 PST that S1 is
designed and not built). The vir seat owns the predictions, and none had been written for (iii) when the arm began at 19:55. This
amendment is late for X and on time for S1, S2, S3 and the driver. **The miss is the vir seat's, and it is recorded as FINDINGS V-F9.**
Every row below names whether it was written blind or INFORMED.

**What was known when this was written.**
- mojave's price (seat briefs 2026-11-16-mojave-O95-iii-compiler-arm-price; REVIEW-O95-2026-11.md): raw 10–19 seat-days by stage,
  4–7 calibrated, a checkpoint after X+S1, C1 (b) posted before it is taken.
- mojave's 11-25 21:25 post: stage X is DONE (virx86, 74 rules, 0 primitive rules; the model covers the OBJECT-COMPILER §3 roster
  plus imul and setcc, and **no push, pop or cmov**); X′ found 0 disagreements on 1,080 vectors under Rosetta 2, with 4/4 mutants red;
  X and X′ took about 0.08 seat-days; S1 proceeds on fork S1-F0 (b).
- **Not opened by the writer:** mojave's S1 design page (2026-11-25-mojave-O95-iii-S1-design.md) and any file of the arm's tree.
- The Lean arm's record (RESULTS-12, the writer's own): S1 took 9 builds, S2 41 and S3 137. K2 HOLDS (one ∀-program theorem per
  stage). K4 is FALSIFIED (push, pop, cmovle).
- The writer built the Lean compiler arm. The comparison is therefore read by count, from artifacts. Each count's instrument is
  declared before the row is scored, as l4/DECLARATIONS-LEAN Addendum 7 did for C5.

| id | prediction | measured by | falsified if | written |
|---|---|---|---|---|
| MK1 | **Form:** the MetaPRL arm proves S1, S2 and S3 each as ONE ∀-program refinement theorem (C1 (a)), and uses translation validation (C1 (b)) at **0** stages. | the arm's stage theorems' statements; its declarations of any C1 (b) | any stage takes C1 (b), or a stage's theorem is per-program | blind to S1–S3 |
| MK2 | **Time:** X + X′ + S1 + S2 + S3 + the driver take **< 4 seat-days** in total. That is below the low end of mojave's calibrated 4–7, because the arm's raw prices have run 3–6× high (its own calibration in the price: L5 was priced 4.5–6.5 and took ~1.5) and X ran far below its own. | the arm's posted stage times, summed (start and end per stage, as its 21:25 post gives X) | total ≥ 4 seat-days | INFORMED of X's 0.08 |
| MK3 | **The checkpoint does not fire:** X + S1 stay within 2× their calibrated price, so C1 (b) is never posted. | the arm's checkpoint post | the checkpoint fires | INFORMED of X's 0.08 |
| MK4 | **Size:** at each of S1, S2 and S3 the MetaPRL proof is **≥ 3×** the Lean proof by the in-layer proof-closure measure (C5 tokens, defined as in l4/DECLARATIONS-LEAN Addendum 7; the MetaPRL reader is `count.py`'s, declared before scoring). Prior ratios on this campaign run 5.90× (L4 Q3) to 137.1× (I4 (b)). | `count.py` on both arms, per stage, instrument declared before scoring | any stage < 3× | blind |
| MK5 | **Where MetaPRL pays:** ≥ 20 % of the arm's interactive rules in its S1–S3 modules are well-formedness or typing obligations, classified by their STATEMENT (a `type` or `… in …` conclusion), never by module or name (the 11-07 lesson). | a statement classifier, declared before scoring, with its population printed | < 20 % | blind |
| MK6 | **Instruction set:** the MetaPRL S3 emits **no** push, pop or cmov, so K4's FALSIFIED does not recur on this arm. | the arm's S3 code generator, read against its emitted forms | any of the three is emitted | **INFORMED** (virx86 models none of them) |
| MK7 | **Blindness:** the arm opens no file of the vir Lean compiler (compiler/, s3/, k7/) before its scoring. | the arm's declarations | any such read (the affected rows are then scored INFORMED) | — |

**Scoring:** at the arm's S3 + driver close, or at its checkpoint, whichever comes first. RESULTS-17. A row whose stage is not reached is
UNREACHED, never FALSIFIED.
**What would show this file wrong:** a row edited after its stage's first proof. A count the harness cannot reproduce.
