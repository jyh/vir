# Compiler S3, vir's half: the word-memory ↔ byte-memory BRIDGE (STATUS-vir 286), the declarations

Written 2026-11-12 by the 67th vir head, BEFORE any bridge file exists. S3 (word code → x86lean `Program` over `stepP`) waits on
paris's C3 library (STATUS-vir 282). This half does not: it relates S2's word memory to x86lean's byte memory and needs nothing
from C3. The object it is checked against is x86lean's `X86/Memory.lean` **at 5f2231f** (read there with `git show`, never from
the shared working tree): `Mem` (a total byte memory, an association list), `read`/`write`, `readN`/`writeN` (little-endian,
byte count as a `Nat`), `readN_congr`. `Val = BitVec 64` (X86/Value.lean at the same sha).

## B-1, what a cell is (S2-M (a), restated, not changed)
An L2 cell is one 64-bit word at the byte address `cellAddr base i = base + 8·i` (VIRC/Word.lean). S2's `WMem = W → W` is read
ONLY at cell addresses. The bridge reads that word as the 8 bytes `readN a 8` at a cell address `a`.

## B-2, the representation relation
`Rep (wm : WMem) (m : X86.Mem) (S : W → Prop) : Prop := ∀ a, S a → m.readN a 8 = wm a`. S is the set of live cell addresses (the
union of the regions' cells). It says nothing about bytes outside S's spans. That is the point: the frame is x86lean's, and the
bridge adds no second frame.

## B-3, the three lemmas the bridge owes (each one ∀-statement; no per-program lemma, K6's spirit)
1. **Round trip:** `(m.writeN a v 8).readN a 8 = v` for every `m`, `a`, `v : Val`.
2. **Disjoint store:** if the 8-byte spans at `a` and `a'` do not meet (`∀ i j < 8, a + i ≠ a' + j` in `BitVec 64`), then
   `(m.writeN a v 8).readN a' 8 = m.readN a' 8`. Proved through x86lean's `read_write_ne` and `readN_congr`, not by unfolding
   the association list (the seam x86lean's file names: the representation may change and the bridge must not notice).
3. **Store preserves Rep:** `Rep wm m S → S a → Sep S → Rep (Function.update wm a v) (m.writeN a v 8) S`. Here
   `Sep S := ∀ a a', S a → S a' → a ≠ a' → spans disjoint`.

## B-4, where Sep comes from, and the premise it costs (declared, so K6 can be read against it)
Sep is NOT assumed per program. It is discharged ONCE from S2's layout premise: regions are disjoint byte ranges that do not wrap
past 2⁶⁴, and each cell is `base + 8·i` with `i < length`. The lemma owed: S2's layout premise ⇒ `Sep (cells of all regions)`.
The no-wrap condition is the premise. It is a statement about the caller's region placement, never about the bytes stored.

## B-5, the project form
A NEW lake project `bridge/` beside `compiler/`, so compiler's counts (K1's population) stay put. It requires x86lean by git at
`5f2231f` (the compose/ precedent: a public repo pinned by sha, never a path into a working tree) and `compiler` by path. Its
packages are APFS-cloned from an existing tree with x86lean's toolchain, manifest by edit, never a bare `lake update`. Every Lean
invocation goes through saltbuild with a logged-build.sh of its own (`bridge/logs/br-NNN.log`).
⚠️ A TOOLCHAIN CHECK IS OWED FIRST: compiler/ is on v4.32.0-rc1 (mathlib's pin). If x86lean at 5f2231f is on a different
toolchain, one project cannot import both. Then this declaration is AMENDED (B-5 only) before any file: the bridge goes into
x86lean's toolchain over a copy of `WMem`'s two definitions, recorded as a copy with its source sha. It is never a silent copy.

**CHECKED the same hour, before any file:** x86lean at 5f2231f is on `leanprover/lean4:v4.32.0-rc1`, compiler/'s toolchain, and
its manifest lists NO packages. One project imports both, and B-5 stands as written.

## What would show the bridge wrong (findings, never routed around)
- a lemma that unfolds `Mem.bytes` (it couples the bridge to x86lean's representation, the seam its author named);
- a premise on stored VALUES (B-4 allows a premise on placement only);
- Sep proved per program rather than once from the layout premise (K6);
- a count or claim taken from x86lean's shared working tree instead of the pinned sha.
