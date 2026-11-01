# Amendment 5 (2026-11-01 01:2x, vir): the C1 token class, split by what a token DOES (row 8, finding L-F1)

⚠️ Written after both arms' first green. No P threshold changes. This adds columns, and the preregistered total C1 is still reported.
- `C1heq`: `HEq` and `heq_of_eq`. These are transport between TYPES. **This is the column P1's claim is about.**
- `C1arith`: `Nat.sub_sub`. It is an arithmetic fact, and it is the same fact whether it re-aligns an index or a value. Whether it is an index use is read from the term it sits in, not from the token.
- `C1rw`: `Eq.mpr` · `▸` · `Eq.rec` · `Eq.ndrec` · `cast`. These are the eliminators that `rw`, `subst` and `cases` emit for ANY equation. They count as transport only inside a lemma whose statement is an HEq (as in `Slice.heq_of` / `Slice.congr_heq`).
- MetaPRL: every column is 0 by construction (no such terms). This is stated, not measured.
**Scoring P1/P1b under amend-5:** P1 on `C1heq` of the L-IDX slice_fuse path. P1b on `C1heq` of L-FLAT.
