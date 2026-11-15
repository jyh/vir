# K7, the stage record (STATUS-vir 301; compiler/DECLARATIONS-K7.md)

- **K7-a PROVED (70th head, 2026-11-12): `router_refines`** (k7/K7/Router.lean, k7-001 EXIT=0, first attempt). It instantiates
  compile_refines' three clauses at the L3 router F (Γ₀ = [tcap], vs = [cap p]) with k5's generic scaled loader (`loader_ok`). The
  premises are on the caller's world: WF, regions placed in [0, 2⁶⁰), cells in range, and the router's cap region at p. The overflow
  disjunct stays, as declared.
- **No router-specific lemma.** The file holds the four evaluation facts (`F_wfB`, `F_fnOk`, `F_ok2`, `F_table`, each `decide`), one
  generic EnvRel lemma for a cap parameter at ANY table (`envRel_cap1`, which names no program), and the instantiation. Nothing mentions
  F's structure, layout or cells.
- **Audit k7-audit-001:** 6 rows. The four evaluation facts read [propext]; envRel_cap1 and router_refines read
  [propext, Classical.choice, Quot.sound]. Control k7-audit-control-001 reads [sorryAx].
- **Going red (k7-probe-mut-001):** `Tm.ok2 F = false` is REFUSED by decide (line 5, EXIT=1). The second mutant, "table length < 2",
  was NOT refused, because it is TRUE for F: the router's lowered table has fewer than 2 entries, while DEFLATE's has at least 2 (its
  twin mutant was refused, k5p-probe-mut-stepT-1). So it is no red control, and only the ok2 mutant counts.
- **Project:** k7/ requires compiler, l3 and k5 by path. Packages are APFS-cloned from k5/ and the manifest was written by edit. Logs go
  through k5's replay filter from k7-001 (k7/logged-build.sh).
- **K7 itself** (the x86 machine, the five exits witnessed, A.4's verdict reproduced) waits on S3, which waits on paris's C3 library
  (STATUS-vir 282).

## The driver theorem's L2 half (STATUS-vir 304; compiler/DECLARATIONS-DRIVER.md, declared at a52e63f/20c303c before the file)
- **DR-1 `compile_refines_mem` PROVED** (k7/K7/Driver.lean, k7-004 EXIT=0). It is compile_refines (1) with `Layout σ' lay ∧ MemRel lay σ'
  m'` at the final store and memory, and it closes finding DR-0 (Sim2's `SRel.done` carries no memory relation) without editing
  Sim2/S2/Compose. The route: the last IR step is S1's `ret` from a matched run state (`match_ret`), where `SRel.run` carries
  Layout/MemRel, and the one `stepW` case that produces `done` keeps the memory (`stepW_done_mem`).
- **DR-2 `driver_l2` PROVED** (k7-005 EXIT=0, first attempt; root k7-006). For any step-shaped e (`[tcap] ⊢ e : tcap` plus the
  compiler's side conditions), k chained ⟶₂ runs (`IterRel`) are matched by k chained word runs that all finish (`WDone`, each run's
  result words being the next call's argument words, i.e. the driver loop), ending at a memory related to the final store. The
  alternative is i < k finished runs and then a run reaching OVERFLOW. **Simpler than declared:** no "regions preserved" premise is
  needed, because the returned capability's `VRel.cap` gives its region length at the new store, which is the next call's EnvRel.
- **Audit k7-audit-002:** 11 rows (5 within the three, 1 [propext, Quot.sound], 5 [propext]), 0 sorryAx. **Going red**
  (k7-probe-mut-002): the end-state clause claimed at the INITIAL memory m instead of the final m' is refused (line 11, EXIT=1).
- **K3 reading of the new statements, and a fix to the instrument.** k5/tools/k3_check.py blacklisted a hand-typed list, which (its
  declared limit) missed `K7.*`. The forbidden set is now DERIVED from every namespace the repo declares (`git grep '^namespace '`),
  minus VIRC/VIRL1/VIRL2/X86. Re-run (k7-probe-K3-001): `compile_refines_mem` OK (60 constants); **`driver_l2` FALSIFIED: it names
  `K7.IterRel` and `K7.WDone`**, generic definitions in a namespace the whitelist does not admit. The positive control router_refines
  reads FALSIFIED (VIRL3.F, K5.*). The S1∘S2 statements of row 296 re-read OK under the derived set (k5p-probe-K3-1), so that
  provisional reading stands.
  ⇒ **OWED at S3** (where K3 is scored): home `IterRel`, `WDone` and `compile_refines_mem` in compiler/ (VIRC), as a file declared in
  DECLARATIONS-S2's "Added" list before it exists, so that the driver theorem's statement names only whitelisted constants.
- **DR-3 `deflate_driver` PROVED** (k7/K7/DeflateDriver.lean, k7-008 EXIT=0; root k7-009; declared in DECLARATIONS-DRIVER Addendum 2
  at 4046221). For bytes < 256, n and OUTMAX < 2³², a region at 0 ≤ p with p + L0 ≤ 2⁶⁰, and every k with `iterS p k init = some σ`:
  the compiled step run k times by the driver loop from `scaleMem init` (each call fed the previous call's returned words) FINISHES all
  k times, and the final memory satisfies `MemRel scaleLay σ m'`. There is NO overflow branch, because `deflate_noovf` excludes it at
  every reached σ_k. The returned words are `capWords scaleLay p L0` at each call (`envRel_cap_inv` plus `reach_shape`). This is the
  word-machine (S2) half of C0 (a) for DEFLATE; the x86 machine half is paris's (S3).
- **Audit k7-audit-003:** 15 rows (8 within the three, 2 [propext, Quot.sound], 5 [propext]), 0 sorryAx. **Going red, weak form**
  (k7-probe-mut-003): the same proof with `n < 2³²` dropped is refused at its 4 uses of the bound. That shows the proof DEPENDS on
  it, not that the theorem is false without it.
- **Row 307, the K3 homing DONE (k3home branch).** The driver's generic definitions and theorems MOVED to compiler/VIRC/Driver.lean
  (namespace VIRC; declared first in DECLARATIONS-S2 "Added"), unchanged in statement: drv-001 EXIT=0 (compiler log, raw: the replay
  filter is declared for k5/k7 only). k7/K7/Driver.lean is now an import stub, and DeflateDriver uses VIRC.WDone.snoc. Root k7-010
  EXIT=0; audit k7-audit-004 15 rows within the three, 0 sorryAx. **K3 re-read (k7-probe-K3-002, derived whitelist):
  `VIRC.driver_l2` OK (56 constants), `VIRC.compile_refines_mem` OK (60); control router_refines FALSIFIED.** The driver
  statement's L2 half now names only whitelisted constants. K3 itself is still scored at S3, on the assembled driver theorem.

## K7-b1, the router through S3 (79th head, 2026-11-15; DECLARATIONS-K7 Addendum 1, declared before the file)
- **`router_x86` PROVED** (k7/K7/RouterX86.lean, k7-012 EXIT=0; k7-011 red on a docstring placed before `set_option … in`; root
  k7-013). `S3.compile_x86` at F with k5's loader: for every WF world placed in [0, 2⁶⁰) with in-range cells and the cap region at
  p, and `lower3`'s code under S3's layout premises with |BUF| ≥ 5, the three clauses hold at the x86 machine (finish → returned
  stDone with the words related to the value, or OVF; fault → FAULT or OVF; k source steps → ≥ k `stepP` steps or OVF; RES with
  `ResWhy` beside each).
- **Evaluation facts only:** `F_need` (needW of F's main ≤ 5) and `F_tbl_nil` (F's lowered table is empty), both `decide`, read
  off first by k7-probe-need-001 (`#eval`: 5 and []). No lemma about F's structure, layout or cells.
- **Premises that stay:** the code-size bound (it names the abstract encoder length), S3's layout facts, `DriverCall` on F's
  cap words, L.live ⊇ Live σ scaleLay. The OVF and RES disjuncts stay.
- **Audit k7-audit-005:** 18 rows; F_need and F_tbl_nil read [propext], router_x86 reads the three; 0 sorryAx.
- **Project:** k7 now requires ../s3 by path (manifest by edit: s3, x86lean at 4f08f91 inherited, bridge inherited; x86lean
  APFS-cloned from s3/.lake).
- **K7 itself stays OWED:** the five exits witnessed at the machine (K7-b2) needs OVF and RES excluded per witness.

## K7-b2 piece (1), RES excluded generically (79th head; DECLARATIONS-K7 Addendum 2, declared before the file)
- **`S3.res_free` / `S3.resWhy_false` PROVED** (s3/S3/ResFree.lean; s3-136 EXIT=0, s3-134 red; audit s3-audit-020 94/94 within
  the three). Static measures on WCode (`rW`, `envM`, `frD`) and potentials over the pending frames (`topM`, `topF`) never increase
  under `stepW` with an EMPTY table (`top_step`); so along every word run from main the ENV words (with `grow`) are at most
  `envM main |ρ₀|` and the frames at most `frD main`, and a layout sized from them makes `ResWhy` false at every reached state.
  Names no program. The router's table is empty (`F_tbl_nil`), so it applies to F.
- **Going red** (s3-probe-mut-001): `envM`'s load clause with its `+1` dropped is refused at two places (envM_mono's load case,
  line 46; top_step's load case, line 147; read in the log). The unmutated copy (s3-probe-ctl-001) is green.
- **Pieces (2)–(4) OWED:** a finishing source run per witness (termination + progress for fix-free terms, then L3's R4 for the
  CODE value), OVF excluded per witness, and the assembly.

## K7-b2 pieces (2)–(4): the five exits witnessed at the machine (79th head; DECLARATIONS-K7 Addendum 3, declared before the files)
- **`K7.five_exits` PROVED** (k7/K7/RouterExits.lean, k7-018 EXIT=0, first build; root k7-019; audit k7-audit-006 24/24, 0
  sorryAx). For F's lowered code P under the shared S3 premises (`Rig`: S3's layout facts, |BUF| ≥ 5, ENV ≥ 8 · envM(F's main, 2),
  STACK room for frD + 2 frames) and L.live covering a W87 world's live cells: each of A.4's five inputs (sender 0, topic 0, on
  L3's 87-cell world), run by the machine from DriverCall on its loader image, RETURNS DONE with its CODE word at cell 1's scaled
  address: truncated (LEN 10) → 1 · bad magic → 2 · ACL bit 0 → 2 · no tokens → 2 · emit → 0. These are A.4's labels under V5's
  mapping (the VIR has one code for the last three drops).
- **Route (`exit_code`, generic in the world):** the source run from `run₂` (`run₂_steps`), SrcInRange from k5's checked runner
  (`srcInRange_of_runC`) ⇒ OVF excluded (`compile_noovf`); `compile_refines_mem_R` gives MemRel at the final store with σ.R kept;
  `s3_refines_from_s2` gives R3 at DONE or RES, and RES is excluded by `resWhy_false` (F's table is empty). The CODE word is read
  through Common's Rep on L.live and MemRel.
- **Per-witness facts are evaluation only** (`rfl`: the two runs reach `ret ⟨0⟩` in 80 steps, the CODE cell's value) plus the
  world-builder lemmas of World.lean (W87 ⇒ WF, Placed, CellsInR; about `mkWorld`, not F).
- **Going red** (k7-probe-mut-exits-001): CODE claimed 2 for truncated and 2 for emit is refused at both lines; the control with
  the right values (k7-probe-ctl-exits-001) is green.
- **A LOST LOG (self-finding):** one run of probes/CtlExits.lean was fired under a throwaway name and its log was then deleted by
  the 79th head. It is recorded in the fleet saltbuild audit log at 2026-11-15 03:47:55 (`args=probes/CtlExits.lean`, EXIT=0, line
  53258). k7's C6 count of logged runs is one short of the runs made.
- **Limits, stated:** (a) "the L3 router triple carried to the machine" holds in R4's own partial-correctness form through
  `router_x86` (every finishing source run is matched), but OVF is excluded only at the five witnesses, not for every world (the
  router's SrcInRange in general is not proved); (b) whether `exit_code`, `Rig` and `five_exits` count as "the instantiation" and not
  as router-specific lemmas is the author's reading (they mention F only through its evaluation facts and generic theorems); a
  non-author read is owed.

## ADDENDUM (2026-11-15, the 80th head): limit (a)'s OVF clause lifted for every world (DECLARATIONS-K7 Addendum 4, STATUS-vir 361)
- **`router_inR` (K7/RouterAll.lean):** F's SrcInRange for EVERY world σ with `W87 σ` and the wire premise `WireB σ` (cells 3 … 66
  hold bytes in [0, 256), inputs/L3-programs.md). No premise on LEN, magic, ACL, tokens, sender or topic. A load outside the
  region (sender·4 + topic ≥ 20, or sender ≥ 4) is a stuck configuration with an in-range head, in range by `srcInRange_stuck`
  (from `step₂_complete`). The proof is a symbolic walk on `World σ 0 f` (L3's Sym.lean form), one checked step at a time,
  splitting on LEN ≥ 24, the two load bounds and the three emit conjuncts.
- **`exit_code_all`:** `exit_code`'s conclusion with `run₂C` replaced by `WireB σ`. The source run to `ret ⟨0⟩` stays a premise
  (partial correctness, as R4 is). So the machine returns DONE with the CODE word at cell 1's scaled address on EVERY W87 world with
  the wire premise on which F's source run finishes, with OVF excluded generically.
- **K7's score does not move and RouterExits.lean is not edited:** `router_inR` is a lemma about F's structure, so by Addendum 3's
  rule it is reported beside K7, not inside it. Limit (a) now reads: OVF is excluded for every W87 world with the wire premise;
  what remains open is TERMINATION (every such world's run reaches `ret`, or sticks at an out-of-region load), which R4 at the
  machine for all worlds also needs.
- **Builds:** k7-020 (K7.RouterAll) EXIT=0; k7-021 (root) EXIT=0; k7-audit-007 28/28 constants within propext · Classical.choice
  · Quot.sound (router_inR_f, router_inR, exit_code_all, srcInRange_stuck all three). **Going red:** k7-probe-mut-inR-001,
  router_inR_f's walk with the wire premise dropped, EXIT=1 at the RD32 sum's let (its range obligation does not close).
- **Probes:** k7-probe-inR-001 … 008 (the walk, explored before the file; 008 EXIT=0 with no sorry). **Sources kept for 001 and 008
  only:** probes 002–007 were each edited forward under the next name (`mv`), so their sources are not in the tree; each run's
  source sha is in the fleet saltbuild audit log, and each log is committed. C6 counts all eight.

## ADDENDUM (2026-11-15, the 80th head): R4 at the machine for every world, TOTAL on R4's premises (DECLARATIONS-K7 Addendum 5, STATUS-vir 361 part 2)
- **`router_R4_x86` (K7/RouterR4.lean):** for EVERY σ with `W87 σ`, `WireB σ` and R4's own premises (SvA < 4, TvA < 4 on σ's
  cells), and a machine in DriverCall on σ's loader image under Rig's S3 premises with L.live covering σ's live cells: ∃ mm, the
  machine RETURNS DONE and every cell i < 87 is at its scaled address with value `postF (cells σ) 0 i`, R4's post-state.
- **Route:** `router_halts` (termination: a symbolic walk with a `Halts` step lemma; under R4's premises no load leaves the region)
  · `router_post` (L3's `R4` used as proved, at frame ∅, from `w87_regionAt`) · `exit_cells_all` (exit_code_all's route with every
  cell, not only CODE) · OVF by `router_inR`, RES by `resWhy_false`. l3 is not edited.
- **K7 limit (a) is now CLOSED for R4's premise set:** the L3 router triple holds at the machine as total correctness for every world
  satisfying it. Outside R4's premises (sender ≥ 4 or an ACL index past the region), the source run sticks at an out-of-region load:
  OVF is still excluded there (`router_inR`) but no DONE is claimed. K7's score does not move (a router result, beside K7).
- **Builds:** k7-022 (root) EXIT=0; k7-audit-008 32/32 constants within propext · Classical.choice · Quot.sound. Probes
  k7-probe-R4-001 … 004 (sources R4a, R4b, R4c, R4d all kept; 004 EXIT=0, no sorry). **Going red:** k7-probe-mut-R4-001, the walk
  with the sender bound widened to < 5, EXIT=1: at each `halts_ret` the configuration is still a load, not a `ret`.

## ADDENDUM (2026-11-15, the 80th head): DEFLATE at the x86 machine (DECLARATIONS-DRIVER Addendum 7, STATUS-vir 369)
- **`deflate_x86` (K7/DeflateX86.lean):** `S3.driver_x86_R` instantiated at DEFLATE's stepT from the loader's image of
  `initStore b om lit p`, under DEFLATE's premises (bytes < 256; n, OUTMAX < 2³²; 0 ≤ p; p + L0 ≤ 2⁶⁰) and the driver's S3 premises
  on stepT's lowering, kept as premises. For every k with `iterS p k (initStore …) = some σ`, the machine reaches the loop head again
  with memory related to σ, OR some iteration leaves the loop at X with a non-DONE status. `iterS_iterRel` turns DEFLATE's iteration
  into the driver's IterRel.
- **Declared limit, unchanged:** the non-DONE disjunct is not excluded. The driver does not name the status, so `deflate_noovf` (S2)
  cannot be applied through it, and RES is not excluded generically (stepT's table is not empty). This is the x86 half of C0 (a) for
  DEFLATE in the driver's own disjunctive form. It is NOT DONE-only.
- **Builds:** k7-023 and k7-024 EXIT=1 (implicit arguments of `deflate_noovf_loaded` and `reach_shape` not inferred); k7-025
  (K7.DeflateX86) EXIT=0; k7-026 (root) EXIT=0; k7-audit-009 34/34 within propext · Classical.choice · Quot.sound. **Going red:**
  k7-probe-mut-dx86-001, the same statement with the machine's start words ρw0 not the loader's, EXIT=1 at `hA` (type mismatch:
  EnvRel holds for capWords only). k7-023 and k7-024 are redacted (home path → `~/fleet`, as earlier logs are).

## ADDENDUM (2026-11-15, the 80th head): DEFLATE at the x86 machine with OVF EXCLUDED (DECLARATIONS-DRIVER Addendum 8, STATUS-vir 371)
- **`deflate_x86_N` (K7/DeflateX86N.lean):** for every k with `iterS p k (initStore …) = some σ`, the machine reaches the loop head
  with memory related to σ (EnvRel, Layout, MemRel, σ.R = σ₀.R), OR it has left the loop at X with cb = **stRes**. This is induction
  on k with `S3.drv_iter_N` at each step: SrcInRange from K5's `deflate_inrange`, L.live carried by σ.R. **OVF is excluded at the
  machine for DEFLATE. RES (ENV or STACK outgrown) is the one non-DONE exit left, and it is not excluded.** This supersedes
  `deflate_x86`'s disjunct; deflate_x86 stays as proved.
- **Builds:** k7-027 (K7.DeflateX86N) EXIT=0; k7-028 (root) EXIT=0; k7-audit-010 36/36 within propext · Classical.choice ·
  Quot.sound. The mutant is s3's (compiler/STAGE-S3.md, drv_iter_N).

## ADDENDUM (2026-11-15, the 80th head): the router SERVED k times at the machine, DONE-only (DECLARATIONS-K7 Addendum 6, STATUS-vir 374)
- **`router_served_x86` (K7/RouterDriver.lean):** for every σ with `RInv σ` (W87, wire bytes, sender < 4, topic < 4), the driver's
  S3 premises on F's lowering plus ENV and STACK room for F's main, L.live covering σ's live cells, and a machine at the loop head on
  σ's loader image: for EVERY k, F's iteration reaches some σk (`router_iter`) and the machine is at the loop head again after k
  calls, its memory related to σk. **No call ends in OVF, RES or FAULT.**
- **Route:** `router_inv_step` (one finishing call keeps RInv: F writes only cells 1 and 2 and the bucket, all outside the wire
  cells; the post-state from `router_post_s`, R5_contents for the unchanged cells, `postF_inR` for the range) · `router_iter`
  (router_halts at every call) · `router_driver` (induction on IterRel, `drv_iter_D` at each call with SrcInRange from router_inR).
- **`drv_iter_D` (K7/DriverD.lean, generic, names no program):** drv_iter_N for an empty lowered table under ENV/STACK room, with
  NO exit disjunct; RES is closed by `resWhy_false`.
- **Builds:** k7-029 (K7.DriverD) EXIT=0; k7-030 (K7.RouterDriver) EXIT=0, first build; k7-031 (root) EXIT=0; k7-audit-011 41/41
  within propext · Classical.choice · Quot.sound, 0 sorryAx. **Going red:** k7-probe-mut-drvD-001 (empty-table premise dropped)
  EXIT=1 at `Unknown identifier htbl`, which is weak. k7-probe-mut-drvD-002 removes the rewrite to [] as well: EXIT=1 at
  `resWhy_false hj`, type mismatch, because `resWhy_false` takes a run over the EMPTY table and F's general table is refused.
