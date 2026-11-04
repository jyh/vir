# L3 inputs — the router as L2 terms (OBJECT-L3, G1–G4 ruled (a))

Drafted 2026-11-03 by the 16th vir head; PINNED 2026-11-03 by the 17th with `object-L3/OBJECT-L3.md`, in the same commit,
BEFORE either arm's first L3 file; both arms receive the same bytes. Concrete syntax is OBJECT-L1 §2's with L2's effect binder.
**The numerals are FIXED at this pin: NW = 64, NS = 4, NT = 4** (the draft's proposal, taken as written), so A = 67 and K = 83,
and `world` has 87 cells. Changed from the draft: this paragraph, the title line, the layout heading's "proposed", and R2's
reference to the draft (now OBJECT-L3 §2).

## Layout of `world` (G1(a), G2(a), G3(a)); numerals NW = 64, NS = 4, NT = 4 (fixed at the pin)
| cells | holds |
|---|---|
| 0 | LEN, the frame's length in bytes (LEN ≤ NW) |
| 1 | CODE, written at every exit: 0 emitted · 1 TRUNCATED_FRAME · 2 UNAUTHORIZED_OR_RATE_LIMITED |
| 2 | PAY, the payload slice's offset, written on emit only (24) |
| 3 … 3+NW−1 | the wire: byte i of the frame at cell 3+i, each in [0, 256) |
| A = 3+NW … A+NS·NT−1 | the ACL: cell A + s·NT + t is 1 iff sender s may publish on topic t, else 0 |
| K = A+NS·NT … K+NS−1 | the buckets: cell K + s holds sender s's tokens |

## Macros (expanded textually before either arm reads a term; they are notation, not syntax)
- `RD32(o, x) e` := `let x0:int ← load(w, 3+o) in let x1:int ← load(w, 4+o) in let x2:int ← load(w, 5+o) in
  let x3:int ← load(w, 6+o) in let x:int = ret add(x0, add(mul(256, x1), add(mul(65536, x2), mul(16777216, x3)))) in e`
  (fresh names per use; `3+o` etc. are numerals).
- `EXIT(c)` := `let w′:cap ← store(w, 1, c) in ret w′`.
- `EMIT` := `let w′:cap ← store(w, 1, 0) in let w″:cap ← store(w′, 2, 24) in ret w″`.
In both terms `w` is the one free variable, Γ ; Δ = (w : cap) ; {w}, and the type is `cap`.

## F (A.3's fused term)
```
let n:int ← load(w, 0) in
if le(24, n) then
  RD32(0, magic) RD32(4, sender) RD32(8, topic)
  let a:int ← load(w, add(A, add(mul(sender, NT), topic))) in
  let t:int ← load(w, add(K, sender)) in
  if and(eq(magic, 1297303345), and(eq(a, 1), lt(0, t))) then
    let w1:cap ← store(w, add(K, sender), sub(t, 1)) in EMIT[w1/w]
  else EXIT(2)
else EXIT(1)
```
## U (virp's I3, I2's specs composed in their order: header, rate limit, ACL, payload)
```
let n:int ← load(w, 0) in
if le(24, n) then
  RD32(0, magic)
  if eq(magic, 1297303345) then
    RD32(4, sender) RD32(8, topic)
    let t:int ← load(w, add(K, sender)) in
    if lt(0, t) then
      let w1:cap ← store(w, add(K, sender), sub(t, 1)) in
      let a:int ← load(w1, add(A, add(mul(sender, NT), topic))) in
      if eq(a, 1) then EMIT[w1/w] else EXIT(2)[w1/w]
    else EXIT(2)
  else EXIT(2)
else EXIT(1)
```
## Rows (each arm proves the typing or its refutation, the meaning, and the triple named)
| id | statement |
|---|---|
| R1 | `(w:cap) ; {w} ⊢₂ F : cap` and the same for U |
| R2 | **G4 (OBJECT-L3 §2): `⟦U⟧₂ ≠ ⟦F⟧₂`**, witnessed by one frame with tokens and no ACL bit: U's bucket cell is decremented, F's is not. virp's `U_eq_F` held because its `drop` ABORTED; an L2 exit keeps its stores. |
| R3 | `U_tx` := U with its post-decrement `EXIT(2)` preceded by `store(w1, add(K, sender), t)` (the decrement undone): `⟦U_tx⟧₂ σ = ⟦F⟧₂ σ` for every σ |
| R4 | the router triple of OBJECT-L3 §3.3 for F |
| R5 | the frame property, OBJECT-L3 §3.4 |
| R6 | run_tokens, OBJECT-L3 §3.5 |
| R7 | F with `EXIT(1)` replaced by `ret 1`: ILL-TYPED (the world is leaked) |
| R8 | F on a frame with magic correct and sender = NS: typed, and it INDEX-FAULTS at the bucket load; no triple holds |

Notes: F loads the ACL and bucket cells BEFORE its guard (ANF), where A.3 evaluates the three conjuncts together; on a frame
with a wrong magic and an out-of-range sender, F index-faults where A.3 drops. G3(a)'s precondition (sender < NS ∧ topic < NT)
excludes that frame, so the triple is unaffected, and R8 is chosen with a correct magic so that it tests the bound alone.
