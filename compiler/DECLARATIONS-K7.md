# K7, the declarations (amend-23 K7; STATUS-vir 301), written BEFORE any k7/ file

Written 2026-11-12 by the 70th vir head. **K7:** *"The router as an L2 term (inputs/L3-programs.md, F at NW = 64, NS = 4, NT = 4),
compiled by the compiler, reproduces A.4's verdict. Its five exits are witnessed, as in paris's hand lowering of program 1, and the
L3 router triple is carried to the machine with no router-specific lemma."* Falsified if a router-specific lemma is needed, or an exit
is not witnessed.

## K7-a, the S1∘S2 half (the x86 half waits on S3, STATUS-vir 282)
- **The instance.** `F` is `l3/VIRL3/Router.lean`'s term (`Fn.c ["w"]`), typed `HasType₂ [tcap] [true] F tcap` (`F_typed`).
  Γ₀ = [tcap], Δ₀ = [true], vs = [cap p], ρw₀ = the cap's two words, as at DEFLATE (Addendum 6 of DECLARATIONS-K5.md).
- **Per-program facts, closed by evaluation only:** `Tm.wfB 1 F`, `Tm.fnOk F`, `Tm.ok2 F`, F's lowered table length < 2⁶⁴, and
  `instL 0 [cap p] F = F.subst 0 (cap p)`. A fact that does not close by evaluation is a finding.
- **The loader:** k5's generic `loader_ok` (L-1, no DEFLATE constant), at a WF store whose regions lie in [0, 2⁶⁰) and whose cells
  are in range. These are premises on the caller's WORLD (it is the router's input) and its placement, stated as such.
- **Statement.** `router_refines`: for every such σ with `σ.R.lookup p = some n`, compile_refines' three clauses hold for the ⟶₂ run of
  `instL 0 [cap p] F` from σ against the word run from `(.run (lower2T [tcap] F []).1 (capWords scaleLay p n) [], scaleMem σ)`.
  The overflow disjunct STAYS. Removing it needs the router's own SrcInRange (its counters' arithmetic), which is not claimed here.
- **Project.** A new lake project `k7/` that requires `../compiler`, `../l3` and `../k5` (for the generic loader) by path. Packages
  are APFS-cloned from k5 and the manifest is written by edit, never a bare lake update. k5/ and compiler/ are not edited.
- **"No router-specific lemma", read here:** the k7/ file may contain only (i) the evaluation facts above and (ii) the one
  instantiation theorem. Any lemma that mentions F's structure, the router's layout, or its cells counts as router-specific and is
  reported against K7.
- **What would show it wrong:** an evaluation fact that fails (wfB/fnOk/ok2 false at F: a finding about the L3 term or the S2
  predicate); a router-specific lemma being needed; `F_typed`'s context not being [tcap].

## ADDENDUM 1 (2026-11-15, the 79th head, before any K7-b file): K7 at the machine, in two parts
- **K7-b1 `router_x86`** (k7/K7/RouterX86.lean): `S3.compile_x86` instantiated at F exactly as K7-a instantiates compile_refines
  (Γ₀ = [tcap], vs = [cap p], ρw₀ = `capWords scaleLay p n`, m = `scaleMem σ`, the loader's Layout/MemRel), lowered by `lower3` at
  `base`. New per-program facts, closed by evaluation only: `needW` of F's main and of every table body ≤ a NUMBER c, read off by
  `decide` (c is printed by the build; L.bufN ≥ c is then a layout premise). The code-size premise `bytes … < 2⁶⁴` stays a premise:
  it mentions the abstract encoder length `ilen`, so it does not close by evaluation; a generic lemma (`blen ≤ 15` ⇒ bytes ≤ 15 ×
  instruction count) would remove it and is not claimed here. S3's layout premises (L.Ok, canonical addresses, the stub's return
  point, DriverCall, L.live ⊇ Live σ scaleLay) stay premises on the caller. The OVF and RES disjuncts STAY.
- **"No router-specific lemma"** is read as in K7-a: the file may hold only evaluation facts and the one instantiation.
- **K7-b2, the five exits witnessed (NOT in this addendum's build):** the five are A.4's five witness INPUTS (virp/VIRP/Exits.lean,
  from compose/Compose/Drops.lean's bytes, sender 0, topic 0): truncated (LEN 10), bad magic, ACL bit 0, 0 tokens, and emit. F has
  ONE EXIT(2) site (its guard is the conjunction), so three of the five land on the same site with CODE 2, as the VIR's one code for
  them already says (V5's mapping). For each input, a world whose source run reaches its exit, carried to a machine run that returns
  stDone with the exit's CODE word in memory. *(Corrected by its author before any K7-b2 file: the first text said "EXIT(2) at its
  three sites", which is U's shape, not F's.)* That needs, per witness, OVF excluded (the router's own SrcInRange, not claimed by K7-a) and RES excluded (a
  bound on the reached word states' ENV/STACK size against the layout). Each is a separate declaration before its file; whether
  any of it needs a router-specific lemma is exactly what K7 scores.

## ADDENDUM 2 (2026-11-15, the 79th head, BEFORE s3/S3/ResFree.lean): K7-b2's route, and its first generic piece
- **Route, four pieces, each declared before its file:** (1) RES excluded — GENERIC (this addendum); (2) a finishing source run
  exists for each witness (L3's `R4` gives no fault and CODE = postF f p at cell 1, but `Triple` is partial correctness, so a
  generic termination + progress lemma for fix-free terms is owed); (3) OVF excluded per witness (the router's SrcInRange at the
  witness worlds); (4) the assembly through `router_x86`/`compile_x86`. Whether (2)–(3) need a router-specific lemma is K7's score.
- **(1) `ResFree.lean` (namespace S3, names no program):** three static measures on `WCode`: `rW` (an upper bound on a returned
  value's width), `envM c n` (the most ENV words, counting `grow`, executing c from n words until it returns) and `frD c` (the most
  frames c pushes). Potentials `topM c n k` and `topF c k` over the pending frames never increase under `stepW` with an EMPTY table
  (`app` is then stuck), and bound the current state. **`res_free`**: along every word run from `(run main ρ₀ [], m)` with tbl = [],
  `|ρ| + kSize k + grow c ≤ envM main |ρ₀|` and `|k| ≤ frD main`; so a layout with `8 · envM main |ρ₀| ≤ env0 − envLo` and STACK
  room for `frD main + 2` frames makes `ResWhy` false at every reached state.
- **What would show it wrong:** a word step whose successor's size exceeds the potential (a measure clause misread); `evalW`'s
  result width differing from `wid` (it is `evalW_length`).

## ADDENDUM 3 (2026-11-15, the 79th head, BEFORE k7/K7/World.lean and k7/K7/RouterExits.lean): K7-b2 pieces (2)–(4)
- **World.lean (about L3's test-world builder `mkWorld`, not about F):** a predicate `W87` (regions = {0 ↦ 87}, the heap's domain =
  [0, 87), every cell in range), true of mkWorld's base and kept by each of its stores when the written value is in range; so
  `mkWorld cells` with in-range values is WF, Placed, CellsInR, with R(0) = 87.
- **RouterExits.lean.** `router_exit` (generic in the world σ at base 0): from a source run to `ret ⟨0⟩` given by `run₂` and a
  checked run given by `run₂C`, under router_x86's S3 premises plus ENV ≥ 8 · envM(F's main, 2) and STACK room for frD + 2
  frames, the machine returns `stDone` with every live cell of σ' (the run's final store) at its scaled address: the CODE cell is
  cell 1. OVF is excluded by `compile_noovf` (SrcInRange from `srcInRange_of_runC`), RES by `resWhy_false` (F's table is empty).
  Then the FIVE witnesses (A.4's inputs on L3's world, sender 0, topic 0, LEN ≤ NW = 64): truncated (LEN 10) → CODE 1; bad magic
  (byte 0 = 0) → 2; ACL bit 0 → 2; 0 tokens → 2; emit → 0. Each witness's facts are evaluation only (`rfl`/`decide`).
- **K7 is scored on these:** HOLDS if all five are witnessed at the machine with no lemma about F's structure, layout or cells
  (world-builder lemmas and evaluation facts are not router lemmas, by K7-a's reading); FALSIFIED if any needs one.

## ADDENDUM 4 (2026-11-15, the 80th head, BEFORE k7/K7/RouterAll.lean; probes k7-probe-inR-001…008 explored the walk first and are counted as runs): STATUS-vir 361, K7 limit (a)
- **`router_inR` (RouterAll.lean): F's SrcInRange for EVERY world**, not only the five witnesses. Premises: `W87 σ` (one 87-cell
  region at base 0, every cell in range) and the WIRE premise of inputs/L3-programs.md (cells 3 … 3+NW−1 hold bytes in [0, 256)).
  Nothing about LEN, magic, ACL, tokens, sender or topic. A run that LOADS outside the region (sender·4 + topic ≥ 20, or sender ≥ 4)
  is stuck there, and a stuck configuration whose head is in range satisfies SrcInRange (`srcInRange_stuck`, from
  `step₂_complete`). Proof: a symbolic walk over the arbitrary world (`World σ 0 f`, L3's Sym.lean form), one checked step at a
  time (`srcInRange_step`), splitting on LEN ≥ 24, the two load bounds, and the three conjuncts of the emit condition.
- **`exit_code_all`:** `exit_code`'s conclusion with the checked-run premise (`run₂C`) replaced by the wire premise: SrcInRange
  comes from `router_inR`, the rest of the route is `exit_code`'s, unchanged. The source run to `ret ⟨0⟩` (`run₂`) stays a premise:
  this is partial correctness, as R4 is. A run that sticks never reaches `ret`.
- **What this does to K7:** limit (a)'s OVF clause is lifted for every W87 world with the wire premise. K7's score does NOT move and
  its route is not edited: `router_inR` IS a lemma about F's structure, so it is outside K7's scoring rule (Addendum 3) and is
  reported beside K7, never inside it. RouterExits.lean is not edited.
- **Going red:** drop the wire premise (cells unconstrained), and the RD32 sums' range obligations must fail to close.

## ADDENDUM 5 (2026-11-15, the 80th head, BEFORE k7/K7/RouterR4.lean): STATUS-vir 361 part 2, R4 at the machine for every world
- **`router_halts`:** for every σ with `W87 σ`, `WireB σ` and R4's own premises (sender < 4 and topic < 4, read from σ's wire
  cells as L3's SvA/TvA read them), F's source run reaches `ret ⟨0⟩`: ∃ k σ', run₂ k (closeW F, σ) = (ret ⟨0⟩, σ'). Same walk as
  router_inR, with a `Halts` step lemma; under these premises no load leaves the region, so no branch sticks.
- **Contents from R4, not re-derived:** σ is `RegionAt 0 87 g σ` for g = σ's cells; L3's `R4` (a Triple, frame ∅) gives the final
  store as `RegionAt 0 87 (postF g 0)`. R4 is used as proved in l3; nothing in l3 is edited.
- **`router_R4_x86`:** for every such world and a machine in DriverCall on its loader image (Rig's S3 premises, L.live covering σ's
  live cells): ∃ mm, the machine RETURNS DONE and EVERY cell i < 87 of the world is at its scaled address with value postF g 0 i.
  This is R4 carried to the machine as TOTAL correctness on R4's own premises (termination from router_halts, OVF from router_inR,
  RES from resWhy_false), for every world, not five.
- **Scoring:** a router-specific result, reported beside K7 (Addendum 3's rule), never inside it; K7's score does not move.
- **Going red:** drop R4's sender bound (sender < 5 admits sender 4, whose bucket load at 83 + 4 = 87 is out of the region), and
  router_halts' walk must fail to close.
