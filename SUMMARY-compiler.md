# O95 — the compiler, summarised (2026-11-15, the 80th vir head)

**What this file is:** one place for the compiler's scoreboard (amend-23 §K) and for the results proved beside it. It makes no
verdict of its own. Every §K cell is copied in short form from RESULTS-12 §K, which copies it from the record that scored it. Every
beside-result names its theorem, its file and its record. There is one arm, the Lean one: the MetaPRL arm builds neither the
compiler nor DEFLATE (amend-23's notes). The writer of the predictions is the builder of the arm.

**The compiler:** VIR (L2) source → S1 (IR) → S2 (word machine) → S3 (x86-64 over x86lean). Composed end to end as
`S3.compile_x86`. Each stage is one ∀-program refinement theorem. Every Lean build runs through `saltbuild.sh`, is judged by its
`saltbuild EXIT=` line, and every audited theorem's axioms are within {propext, Classical.choice, Quot.sound}.

## §K — the verdicts (copied; full cells and sources in RESULTS-12 §K)

| id | prediction (short) | verdict |
|---|---|---|
| K1 | 40 < S1 builds ≤ 80 | **FALSIFIED (low)**: S1 = 9 |
| K2 | each stage one ∀-program theorem, no translation validation | **HOLDS** for S1, S2, S3 (composed: `compile_x86`) |
| K3 | the driver theorem names no program | **HOLDS** on the prediction's falsifier (non-author read, RESULTS-12 Add. 6); the tool's FALSIFIED on S3.* / VIRBridge.Live is an instrument finding beside it |
| K4 | emitted instructions ⊆ §3 ∪ {imul, setcc, jo} | **FALSIFIED**: push, pop, cmovle (all T-exact in x86lean COVERAGE) |
| K5 | OVF unreachable for DEFLATE's step, no per-input premise | **HOLDS** (`deflate_noovf`; strengthened by `deflate_noovf_loaded`) |
| K6 | 0 per-program layout lemmas | **HOLDS** on its declared population |
| K7 | the compiled router reproduces A.4's five exits, and carries the L3 triple to the machine, no router lemma | **HOLDS**, both conjuncts (RESULTS-12 Add. 6): the five exits (non-author read); the triple in partial-correctness form at every capability base p, `router_triple_x86_p` (RESULTS-12 Add. 8; `router_triple_x86` is its p = 0 instance), OVF and RES as stated disjuncts |

## Beside the scoreboard: proved, router- or program-specific, and NOT scores

None of these moves a §K verdict. Each is a lemma about a particular program, so by K7's own rule (DECLARATIONS-K7 Add. 3) it sits
beside K7, never inside it.

| result | theorem (file) | what it says | limit, stated | record |
|---|---|---|---|---|
| OVF for every router world | `K7.router_inR`, `exit_code_all` (k7/K7/RouterAll.lean) | F's SrcInRange on every 87-cell world whose wire cells hold bytes, so OVF is excluded at the machine for every such world, not only at the five witnesses | finishing runs only (partial correctness) | DECLARATIONS-K7 Add. 4; k7/STAGE-K7.md |
| R4 at the machine | `K7.router_R4_x86` (k7/K7/RouterR4.lean) | TOTAL correctness on R4's premises (sender, topic < 4): the machine returns DONE and every one of the 87 cells holds R4's post-state | outside R4's premises the source run sticks at an out-of-region load; no DONE is claimed there | DECLARATIONS-K7 Add. 5; k7/STAGE-K7.md |
| the router served k times | `K7.router_served_x86` (k7/K7/RouterDriver.lean) | for every k, the driver loop returns to its head after k compiled router calls, memory related to the k-th source store; no call ends in OVF, RES or FAULT | ENV/STACK room for F's main and the driver's S3 premises are premises | DECLARATIONS-K7 Add. 6; k7/STAGE-K7.md |
| DEFLATE at the machine | `K7.deflate_x86_N` (k7/K7/DeflateX86N.lean) | for every k steps of DEFLATE's iteration, the machine reaches its loop head with memory related to the k-th store, OR it has exited with RES; **OVF excluded** | **RES is NOT excluded** (4 table functions, all with non-tail calls; no static bound; empirical depth 10 is not a proof). A proof is a K5-scale campaign outside amend-23, posted as a fork (default: leave it a limit) | DECLARATIONS-DRIVER Add. 7–9; k7/STAGE-K7.md |
| generic driver steps | `S3.drv_iter_N` (s3/S3/DriverN.lean), `K7.drv_iter_D` (k7/K7/DriverD.lean) | one driver iteration with OVF excluded (exit RES only); for an empty table, no exit at all | K3's tool reads them FALSIFIED on S3.* only, the same reading as `driver_x86`, under K3's open fork | compiler/STAGE-S3.md; k7/STAGE-K7.md |

## Open, and whose

- ~~**K3 and K7 non-author reads:** the helm's to route.~~ DONE 11-15 by paper (RESULTS-12 Add. 6): K3 HOLDS, K7 conjunct (2) was uncovered and is now proved, D7 HOLDS. D7's byte-type reading is retired by `safety_bytes` and
  `correct_bytes` (deflate/VIRDeflate/Bytes.lean, no premise on the input bytes; RESULTS-12 Add. 7; non-author read by paper; merged in #82).
- **RES for DEFLATE at the machine:** the fork is posted. The default is (B): it stays a stated limit.
- **Findings of the compiler stage:** DECLARATIONS-S3 Addendum 11 (the declared `app` code miscompiled; fixed before any claim
  covered it) and K4's instruction list (push, pop and cmovcc missing). Both are in RESULTS-12 Addendum 1.

## Runs (C6, logged)

Counted by `cat <dir>/logs/*.log | grep -h 'saltbuild EXIT=' | sort | uniq -c` at the commit that adds this file: see RESULTS-12
Addenda 1–5 for each count and the commit it was taken at. Several unlogged or source-less probe runs are stated in k7/STAGE-K7.md.
