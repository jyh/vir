# Program 3 inputs: the SAFETY theorem of Exhibits A.1/A.2 over program 2's fused router (O95, STATUS-vir row 23). The same bytes for both arms

Programs 1–2 proved FUSION (U ≡ F). Program 3 proves the object's own SPEC theorem, which is stated in BOTH logics in the frozen object (`object/exhibits-section5.tex`, Exhibits A.1 and A.2). This is where §5.1 places the "boundary distinction" (Lean's ValidFrame is a pair crossing boundaries through `↑b`/`.val`; CTT's is a WireBuf, with statement well-formedness in Gate 2).
Everything in I1, I5, I7, J1–J4 and amend-1..8 carries over. Written by vir 2026-11-01, **before either arm's first proof on program 3**.

## K1. The router is program 2's F2 (J4), unchanged. No new term.

## K2. ValidFrame, as A.1/A.2 write it
```
ValidFrame ≡ { b : WireBuf | len(b) ≥ 24 ∧ read_u32(b, 0) = MAGIC }     (appendix A, line 18; A.1 as a Lean subtype)
frame_sender(b) ≡ read_u32(b, 4)     frame_topic(b) ≡ read_u32(b, 8)
```
Lean writes it as A.1 does, a subtype of the wire buffer (`{ b : ByteArray // 24 ≤ b.size ∧ … }`). F2 is applied to the frame as a whole-buffer slice. MetaPRL writes it as A.2 does, a set type over WireBuf. Neither arm may choose the other's representation, because that difference is the measurement.

## K3. IsRouted and the goal
```
IsRouted(o) ≡ o is a return{(st', q)}  (not a drop)
K3:  ∀ b : ValidFrame, st.  IsRouted(F2(b, st)) ⇒ can_access(frame_sender(b), frame_topic(b))
```
**Erratum E10 (vir, filed beside this file):** A.1/A.2 write `route(p, b)` with a principal `p` and conclude `CanAccess(p, frame_topic(b))`. Neither F nor F2 takes a principal; both read the sender from the frame. With `p` free and route = F2 the theorem is FALSE, because IsRouted does not depend on p. vir reads `p` as `frame_sender(b)`, the only principal F2 consults. An arm that disputes this reading posts on the bus before its first proof.

## K4. What is scored
The proof of K3 in each arm. The Lean theorem is named `VIR.route_acl_safe` (file `lean/VIR/Router3.lean`). The MetaPRL theorem's files follow the program-2 pattern with suffix 3: theory `vir3.ml`, chain `steps/c2-router3.mp`, replay `runs-c2-router3.txt`.
