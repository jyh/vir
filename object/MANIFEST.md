# vir object — the FROZEN text (O95, STATUS-vir row 1)

Frozen 2026-11-01 by seat vir (first head). **Nothing in `object/*.tex` is ever edited.** An erratum goes in `../errata/`, never here.

## Source
- the fleet's private record repository, commit `f17b69171ab2ae856206e3d33e160d9775da3410`
  ("O94 bundle: apply his 10-31 ask-5 ruling ... rebuild into build-2026-10-31"), the ASK-5 BUILD the boot brief names.
- path `papers/o94/arxiv/o94-verification-agents.tex`, blob `e391aaedd500f1a3e1272cdab723385fe31b17b7`,
  file sha256 `b51cafcb367cf08002a696947c299667522434e3f1f79b6f972f84c2a515249e`, 801 lines.
- ⚠️ paris's A.4 price (bus @[bus]) and mojave's loops price (@[bus]) read the EARLIER commit `87a949f86`.
  Measured: `git diff 87a949f86 f17b69171` changes lines 51 · 85 · 195 · 209 · 262 · 265 · 450 · 461 · 466 · 471 only (`-U0`), none in 333–371 or 474–585, so both priced the same bytes frozen here.

## Files (byte-exact line ranges of the source; `verify-freeze.sh` re-derives them, rc 0 = intact)
| file | source lines | sha256 | content |
|---|---|---|---|
| `appendix-A.tex` | 474–585 | `693552bdf7f250d7c235997c97eb795184b220707a79d1e459b0685bd63b1081` | A.1 ontology · A.2 grammar + 4 rules · A.3 three rewrites + fused term · A.4 lowered asm |
| `exhibits-section5.tex` | 333–371 | `83fc9d157b330cdbcbf6ab7d1e128d589b11b640feaeac05336b8d50b1595387` | §5.1 contrast exhibits (Lean / CTT statements) + §5.2 Exhibit B.1 (the UNFUSED input term) and the paper's HEq-transport claim the predictions test |

## Scope
The brief says "appendix A.1–A.4"; the README and the helm's order say "A.2–A.3". The freeze takes the SUPERSET (A.1–A.4)
plus the §5 exhibits, because A.3's derivation starts from Exhibit B.1 and the Lean-arm prediction is stated in §5.2.
The Lean arm's first act is A.2–A.3 (STATUS row 4); A.4 is paris's spike's object.
