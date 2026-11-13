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
