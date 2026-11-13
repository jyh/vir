# OBJECT-L5 — layer L5, the standard library (J1(a) J2(a) J3(a) J4(a) J5(a))

**Drafted 2026-11-12 by the 70th vir head. PINNED 2026-11-13 by the 71st, BEFORE either arm's first L5 file**, on the Captain's
word at the 11-13 council (ask 1, put to him as *"pin OBJECT-L5 at J1–J5 (a): L1′ first (function types carry the capabilities
their bodies use, with one conservative-extension theorem over L2) · monomorphic, duplication measured · only the routines DEFLATE
and the router already hand-code, scored by re-expressing both · both arms · the compiler's L1′ extension as acceptance, after
S3"*, rec yes, default not pinned). His word: *"yes"*. Every fork is at its recommendation: J1 (a) L1′ is L5's first act · J2 (a)
monomorphic · J3 (a) the routines the two programs already hand-code, with DEFLATE and the router re-expressed over them as the
acceptance · J4 (a) both arms, for L1′ and for the routines · J5 (a) the compiler's L1′ extension is L5's acceptance, after S3.
The text from "The draft's own text" down is the draft byte for byte (its title line says DRAFT, UNPINNED; this header supersedes
it, as at OBJECT-DEFLATE). §1 keeps the forks' arms as the record of what was ruled; the ruled arm is (a) in each. §4 keeps the
pack ask as it was put. **Nothing in this file is edited after its pin.** An erratum goes in `errata/ERRATA-L5.md`. Both arms
receive these bytes and nothing else from each other. Predictions: `predictions/PREDICTIONS-amend-24.md`, written after this
pin and before either arm's first L5 file.

**Declared at the pin (facts read at master caf23c0, none of them a fork):**
- **The symbol L1′ has had three readings in this repository, and this object fixes one.** OBJECT-L2 (status paragraph) used it
  for *"sizes carried by types, the dependent reading"*, NOT commissioned, with *"L4 wanting capabilities in function types"* as
  its reopening trigger. OBJECT-L4 H2(b) used it for *"types indexed by assertions"* (`lock[I]`), not ruled. **Here L1′ is J1 (a)'s
  sentence and only that:** a function type may carry the capabilities its body uses, a fix body is checked with those
  capabilities in Δ, and one conservative-extension theorem over L2 holds. Sizes in types and assertions in types stay NOT
  commissioned; either one would be a new fork at a sitting, not a reading of this pin.
- **§0's wall is OBJECT-L3's (R-b), verbatim there:** *"No capability crosses a function boundary, and a λ/fix body is checked
  with Δ = ∅"* (and OBJECT-L2's typing rules, where the Δ = ∅ clause for λ/fix is stated). L1′ is the change that lifts it.
- **The arms at the pin.** Lean: L4-closed at 4017931 (RESULTS-10), DEFLATE and the compiler on master (RESULTS-11, RESULTS-12).
  MetaPRL: L4-closed at d257d2f29 (RESULTS-10's MetaPRL column); DEFLATE and the compiler were Lean-only (OBJECT-DEFLATE X0 (a)).
  **No L5 file exists on either arm:** `git log --all -S` reads 0 commits for `VIRL5`, `virl5` and `L1prime` in this repository
  (control `VIRL4` 80), and 0 for `virl5` in every MetaPRL-arm working clone that carries the L4 arm (controls `virl4` 170 · 79 · 34).
- **J4's clause *"unless the MetaPRL arm prices them out at the pin"*** is answered by a price the MetaPRL arm posts after this
  pin. A large price goes to the Captain as a pace ruling (§3's one named sitting); it does not edit this object.
- **J5 waits on S3**, which waits on the x86lean C3 library. L1′ and the routines do not wait on it.

The draft's own text:

# OBJECT-L5 — DRAFT, UNPINNED: layer L5, the standard library (the last layer of his 11-02 stack)

**Drafted 2026-11-12 by the 70th vir head (STATUS-vir 306) for his read through the helm, as DEFLATE and the compiler plan were.**
Nothing here binds until his word pins it. Its predictions are written AFTER that word and BEFORE either arm's first L5 file.
His stack (11-02, 17:3x): L1 typed pure core → L2 imperative → L3 the router as an L2 program → L4 locks → **L5 stdlib**. L1–L4 are
scored on both arms (RESULTS-6…10). DEFLATE and the compiler (amend-23) are the first application (RESULTS-12).

## 0. The wall L5 meets first, stated so nobody discovers it in a proof
OBJECT-L3 (R-b): *no capability crosses a function boundary*; a λ/fix body is checked with Δ = ∅. **So no L2 function can loop over
a region.** Copy, fill, compare and scan each read or write a region on every iteration. L3 put its n-call property in the LOGIC.
DEFLATE made one decode STEP the program, with the loop as an induction in the logic and, at the machine, the driver loop (C0 (a),
proved for the word machine this week: `driver_l2`, `deflate_driver`). That works for a program at the top level. **It does not
work for a library**, because a library routine is called from inside other code, not run by a driver. OBJECT-L2 named the trigger
(*"L4 wanting capabilities in function types"*, the L1′ change). DEFLATE was the first program to want it and stepped around it. A
standard library cannot step around it.

## 1. The forks (each with its recommendation; the default fires at his word "yes")
- **J1 — L1′ (capabilities in function types) as L5's first act?** (a) **YES.** L5 opens with L1′: a function type may carry the
  capabilities its body uses, a fix body is checked with those capabilities in Δ, and there is one conservative-extension theorem
  over L2 (every L2 program means what it meant). Then the library is written as ordinary L1′ functions. (b) NO: every routine is a
  step plus the driver, and each caller becomes a driver. Composition is in the logic only, and a routine cannot call a routine.
  **Rec (a).** (b) is what DEFLATE did. It does not compose, and composing is what a library is for.
- **J2 — polymorphism.** L2's cells hold `Int` only (`Store.H : Int → Int`) and its types are simple. (a) **MONOMORPHIC:**
  routines over int regions, with structured data as int encodings, and the duplication MEASURED (how many routines differ only
  in an encoding). (b) parametric polymorphism now, a second language change in the same layer. **Rec (a)**, polymorphism NAMED and
  OWED, triggered by a measured duplication.
- **J3 — what is in it.** (a) **WHAT THE TWO PROGRAMS ALREADY HAND-CODE:** copy (DEFLATE's back-reference copy and stored copy),
  fill, compare, bounded scan, and DEFLATE's bit reader. Acceptance: DEFLATE and the router re-expressed over the library, with the
  original theorems carried over and the code that collapses into calls COUNTED. (b) a general library (lists, maps, strings).
  **Rec (a)**: it is driven by use, and it is scored against two programs whose proofs already exist.
- **J4 — arms.** (a) **BOTH** (Lean and MetaPRL), because L1′ is a language layer and the campaign's comparison is about language
  layers. The library routines go on both as well. (b) Lean only, as DEFLATE was. **Rec (a)** for L1′, and (a) for the routines,
  unless the MetaPRL arm prices them out at the pin.
- **J5 — through the compiler.** L1′ puts capabilities in closures, so S1/S2 change: a closure carries its capability words, and
  K6's layout premise has to cover them. (a) **the compiler's L1′ extension is L5's acceptance**, after S3 (one ∀-program theorem
  per stage again, K2's form, with no per-routine lemma). (b) L5 stays above the compiler. **Rec (a).**

## 2. What would show the layer wrong (findings, never routed round)
L1′ needing an edit of an L1–L4 rule (not conservative) · a routine that needs a premise on its input's contents beyond its region's
size (DEFLATE's D7 shape) · DEFLATE or the router re-expressed over the library needing a new lemma about the library's internals
(the library has not abstracted) · the compiler extension needing a per-routine lemma (K6's spirit).

## 3. Size, as an ESTIMATE (not a measurement)
L1′ on Lean: about one L2-sized arm (~100 builds; L2 took 2–3 heads). On MetaPRL: the arm prices it at the pin. Library routines: ~5
× 20 builds. DEFLATE and the router re-expressed: ~60. Compiler extension: after S3, priced then. **Sittings: 1** (this draft's
forks), plus a pace ruling if the MetaPRL arm's price is large.

## 4. Asks for the pack (≤ 3 lines each)
- O95 · **pin OBJECT-L5 at J1–J5 (a)?** Rec yes: L5 opens with L1′, because a library cannot be step-shaped. DEFAULT: not pinned;
  vir keeps scoring and S3 support, and re-offers at the review after S3.
