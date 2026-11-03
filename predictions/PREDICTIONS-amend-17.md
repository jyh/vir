# PREDICTIONS amendment 17 — W3 (iii), a BLIND extension: the sum type τ₁ + τ₂, its form fixed here for both arms

**Written 2026-11-03 ~06:3x PST by the 14th vir head, BEFORE either arm's W3 (iii) commit.** At this file's commit, no commit on any
vir branch adds a sum type, `inl`, `inr` or `case` to `l1/VIRL1` (read by `git log --all -S` per needle: the hits are `Or.inl` proof terms and K5's function named `sum`, none a sum type), and the MetaPRL arm has posted no L1 extension.
amend-13's W3 (i)/(ii) and amend-15's category names and timing are UNTOUCHED.

## Why this amendment exists (a finding against vir)
The Lean arm made its W3 (i) and (ii) commits (vir 21c2b97, ba9c696) after both arms posted "L1 closed". vir's post announcing them
also CARRIED the Lean (ii) design: projections as atoms, and the count those choices give (3, or 4 as expressions). That post was
addressed to the MetaPRL arm, before the MetaPRL arm had made its own (ii). So amend-15's blindness is broken for (ii), in one
direction, by vir. (ii) stays scored, LABELLED "MetaPRL informed of the Lean design". This amendment adds a third construct that
neither arm has built or discussed, and it fixes the construct's FORM here, so that no placement is left as "the arm's call" for
either arm to read off the other.

## The construct (both arms build exactly this)
- **Type former:** `τ₁ + τ₂`.
- **Injections, ATOMS:** `inl a`, `inr a`. A value when `a` is a value. Typing: `Γ ⊢ a : τ₁ ⟹ Γ ⊢ inl a : τ₁ + τ₂` and symmetrically,
  with the OTHER summand read from an ANNOTATION on the injection (`inl[τ₂] a`, `inr[τ₁] a`), so that typing stays syntax-directed
  and unique (OBJECT-L1 §4's requirement).
- **Elimination, an EXPRESSION that binds one variable in each branch:** `case a of inl x ⇒ e₁ | inr y ⇒ e₂`. Typing:
  `Γ ⊢ a : τ₁ + τ₂,  Γ, x:τ₁ ⊢ e₁ : τ,  Γ, y:τ₂ ⊢ e₂ : τ ⟹ Γ ⊢ case … : τ`.
- **Steps:** `[case-l] case a of … ⟶ e₁[v/x]` if `⟨a⟩ = inl v`; `[case-r]` symmetrically.
- **Meaning:** `Φ(E)(case a of …) = E(e₁[v/x])` when `⟨a⟩ = inl v`, `E(e₂[v/y])` when `⟨a⟩ = inr v`.
- OBJECT-L1's required theorems (uniqueness, weakening, substitution, progress, preservation, determinism, soundness, semantic
  type soundness: eight, across its steps 4–6) are re-established for the extended language, with no fuel and no primitive step rule, as for L1.

## Predictions (scored by `count.py --arm v3l1` on Lean; on MetaPRL by the reader of STATUS-vir row 98, red first, before scoring)
- **W3 (iii): Lean = 4, MetaPRL = 0.** Lean's `Ty`, `Atom`/`Tm`, `Step`/`Atom.eval`, `HasTypeA`/`HasType` and `head`/`Φ` are closed
  definitions, and the construct touches every category (an atom, an expression with a step rule and a Φ clause). On MetaPRL the
  language is an operator list over a parameter, so the construct is an ADDITION. **FALSIFIED if** Lean ≤ 3, or MetaPRL ≥ 1.
- **W3 (iii)b, EXPLORATORY, no direction:** per arm, the lines and rules added or changed outside the four categories (Lean: the
  proof cases; MetaPRL: the new rules and any rule re-proved), reported beside the count.

## Timing and blindness
Each arm makes ONE W3 (iii) commit, after this file is on master, and neither reads the other's (iii) before making its own.
Announcing posts carry the SHA and the COUNT only, never a design note. Each arm's commit message states that its (iii) was made
without reading the other's. The MetaPRL arm declares its four category names (amend-15) before its first extension commit, if it
has not already.

## What would show this unfair
a (iii) commit on either arm before this file's sha is on master · the construct built in a different form from the one above
(another binder shape, the case as an atom, no annotation) without an erratum beside this file · an announcing post that carries
a design note · an arm whose (iii) was made after reading the other's.
