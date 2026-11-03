# L2, the Lean arm's declarations (amend-16, "owed by each arm before its first L2 file")

Written 2026-11-03 by the 15th vir head, on branch l2-lean, ONE commit after the OBJECT-L2 pin (dec0cdd) and BEFORE any
`.lean` file under `l2/`. **SEALED:** the bus carries only this file's commit sha and sha256 until the MetaPRL arm has posted
its own declarations, so that neither arm's representation choices are informed by the other's (FINDINGS V-F5). Both are
quoted into RESULTS-7.

## Where L2 lives
- A SEPARATE lake project `l2/` (lib `VIRL2`), beside `l1/`, requiring `l1` by PATH (`../l1`) and mathlib at salt's pin,
  so L1's own counts stay put. Every build through `l2/logged-build.sh` (saltbuild, one log per run, `l2/logs/`).
- **L1 is IMPORTED, never edited.** W8 / Y2 reads `count.py --arm w8 --prefix l1/VIRL1` with **BASE = vir 37c209e**
  (origin/master at the L2 pin: L1 closed + the three W3 extension commits, which are L1's own record and predate L2). EXT =
  the Lean arm's L2-closed sha.
- Files (planned names; a renamed file is declared again before it is scored): `VIRL2/Sig2.lean` (Σ₂ as an instance of
  L1's `Sig`/`ESig`) · `VIRL2/Store.lean` (stores, alloc/load/store/free as partial functions, their well-formedness) ·
  `VIRL2/Step2.lean` (⟶₂ on configurations) · `VIRL2/Typing2.lean` (⊢₂) · `VIRL2/Denot2.lean` (⟦·⟧₂) ·
  `VIRL2/Logic.lean` (assertions, ∗, triples, the frame rule, the small axioms) · `VIRL2/SemTyping.lean` (semantic typing) ·
  `VIRL2/Conservative.lean` (OBJECT-L2 §7) · `VIRL2/Programs.lean` (M1–M5).

## The store's representation
σ = (H, R) as OBJECT-L2 §2 states it, both components FINITE maps (mathlib `Finmap`, extensional equality): H : addresses
ℤ ↦ ℤ, R : bases ℤ ↦ lengths ℕ. Well-formedness (dom H = ⋃ regions, regions pairwise disjoint, lengths > 0) is a predicate
`Store.WF`, proved preserved by every step, never built into the type. `alloc n` takes the base max(0, max over live (p, n')
of p + n'), the least fresh base above every live region. The runtime capability ⟨p⟩ is a constant of Σ₂ carrying p.

## The linear context Δ and its split
Γ stays L1's `Ctx` (de Bruijn, index 0 innermost); a capability variable is a Γ entry of type `cap`. Δ is a USAGE MASK over
Γ: a list of booleans of Γ's length, `true` = an available linear capability at that index. A binder pushes one entry (true for
a `cap` binder, false otherwise). The split Δ = Δ₁ ⊎ Δ₂ is POINTWISE disjoint partition of the mask. "Exactly once" is: at a
`ret`, the mask is all-false except the returned capability's own index.

## The triple
SEMANTIC, defined from ⟶₂ (not an inductive proof system). Assertions are predicates on store FRAGMENTS (pairs of finite
maps), ∗ is disjoint union of fragments in both components. `{P} e {v. Q}` holds iff for every fragment σ ⊨ P and every
frame σ_f disjoint from it with σ ⊎ σ_f well-formed: no configuration reachable from ⟨e, σ ⊎ σ_f⟩ is stuck unless it is
`ret a`, and every reached `ret a` has a store σ′ ⊎ σ_f with σ′ ⊨ Q[⟨a⟩/v]. The frame rule is then proved from that
definition with no hypothesis about regions e does not touch; the small axioms are proved from the four operations'
locality lemmas.

## The meaning
⟦e⟧₂ : Store → Part (Atom × Store), ONE `Part.fix` of a functional Φ₂ (L1's form with a store); a fault is ⊥ (`Part.none`),
fault ∉ Val (OBJECT-L2 §6 as pinned).
