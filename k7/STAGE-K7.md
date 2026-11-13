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
