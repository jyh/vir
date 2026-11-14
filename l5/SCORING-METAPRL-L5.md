# L5 — how the MetaPRL column is READ (vir, the scorer), written BEFORE any figure is taken from the arm's virl5 modules

Written 2026-11-14 by the 76th vir head. The arm's proofs already exist: mojave/vir-l5 at **2d9a6c7f0**, census row 589 at
@[bus] 08:55, 948 complete grounded and 0 ungrounded. So this reading comes AFTER the arm's proofs and BEFORE any count, which is
what amend-24 asks of an extractor ("added red first, before scoring"). At the time of writing the scorer has read: the arm's
DECLARATIONS-L5-METAPRL.md at 2d9a6c7f0 (G0–G8, A1–A12), the census post, and the arm's A11 post. It has read no virl5 module.
The subject is a scratch clone of the arm's local branch at the pinned sha. The arm's tree is never read in place (FINDINGS V-F2).
LV1's base is the arm's L4-closed sha **d257d2f29**.

| prediction | MetaPRL reading (instrument: `count.py --arm metaprll5 --base d257d2f29 --ext <sha> CLONE`, selftest arm red first) |
|---|---|
| LV1 | Files changed under `theories/vir/virl[1-4]*` between base and ext (git diff --name-only). HOLDS iff 0. A `virl5_*` file that names a `Virl4` module is reported beside. |
| LV2 | `prim` rule declarations in `theories/vir/virl5_*.ml` (a line whose first token is `prim`, OCaml comments stripped first, as ARM29). HOLDS iff 0. Files changed OUTSIDE `theories/vir/` between base and ext are listed beside as framework edits (M-F6's rule). |
| LV3 | The CE theorems as the arm names them (`VIR_L5M_CE`: a typing-half name and a step-half name). Each must exist as an `interactive` statement in a `virl5_*` file and carry status complete in the arm's census. "No premise beyond ⊢₂" is an AUTHOR READ of the two statements, quoted into RESULTS-13 and marked Q, because it is not mechanical here. If the names are not given, the row reads Q. |
| LV4 | UNREACHED by the arm's declaration G7 (semantic typing priced out). Measured: the number of `virl5_sem*` files at ext. Any such file would turn the row into a count, which is declared before it is read. |
| LV5 | Reported, no direction (amend-24). MetaPRL has no transport cast: the row reads "no analogue". |
| LV6 | `[wf]` premise labels per rule statement (interactive or prim, never a rewrite), the reading of amend-21 Q5 (`L4M_WF_RE`). Population: the L1′ rules as the arm names them (`VIR_L5M_LV6`). **DEFAULT if the arm names none:** every interactive/prim rule statement in `virl5_rules`, `virl5_frame` and `virl5_ret`, the program-logic modules over ⟶₅. The L2 side is Q5's own: the six L2 rules of `L4M_Q5_L2` at ext (42/6 at L4). HOLDS iff rate5 ≥ rate2. Every virl5 rule statement is reported beside. |
| LV7 | For each of the arm's 14 triples (`*_triple` and `*_cap` in virl5_triple): the content variables are the statement's binders typed `int -> int` (the `regionv` contents). A content premise is a hypothesis of the statement, other than the triple's own precondition, that names one. HOLDS iff 0 over the five routines LV7 names. `l5_copy_self` is reported BESIDE as the sixth (the arm's G5). |
| LV8, LV9 | Read on the router only (the arm's G6). UNREACHED while no `virl5_router*` file exists at ext (measured), with no verdict. |
| LV10 | A routine's SHAPE: its `define` in virl5_lib together with every virl5_lib `define` it names, transitively (its `_loop` helpers). OCaml comments are stripped and whitespace normalised. The routine's own name stem (`l5_fill` in `l5_fill_loop`) becomes `R`. Every integer literal is erased: decimal digits, the named literals `lit…`, and `venc{…}`'s argument. Variables are identifiers that occur quoted (`'x`) anywhere in the shape, or as a name in a binder list (`x, d1. …`). They are renamed v1, v2, … in order of first occurrence, quoted or not. Operator names are kept. Equal shapes among the five count; `l5_copy_self`'s pairs are BESIDE. HOLDS iff 0. (Amended twice before any count. Binder-list names were added when the selftest fixture showed that an unquoted binder escaped the renaming. A raw text comparison would separate two routines by their helpers' names and their bound-variable names alone.) |
| LV11 | Unscored until S3 (amend-24). |

**What would show this reading unfair:** a figure from a virl5 module quoted before this file's commit · a population changed
after a count · the arm's tree read in place · a Lean L5 file used to decide a MetaPRL row.
