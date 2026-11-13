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
