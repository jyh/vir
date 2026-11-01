# Program 2 inputs: the B.1-faithful router with a DYNAMIC payload (O95; errata E9). The same bytes for both arms

Program 1 (I1–I7, `router-inputs.md`) is the router as A.3's F states it, with the payload at the constant 24.
B.1 ends `emit_payload(b3, hdr.payload_offset)` and A.1 defines `frame_pay_off` (u32 at 12) and `frame_pay_len` (u32 at 16), so program 2 uses them.
Everything in I1, I5, I7 and amend-1..6 carries over unchanged. Only the following is new. Written by vir 2026-11-01 02:1x, **before either arm's first proof on program 2**.

## J1. New declared constants
```
lin/slice op  take{s; n; p. k[p]}        (* the first n bytes of s as a slice; needs n ≤ len(s) *)
code          ERR_BAD_PAYLOAD            (* distinct from the two codes of I1 *)
atoms         24 ≤ off · off + n ≤ len(b) (relops over the read values, as A.2 allows)
```

## J2. The new and changed spec bodies (I2's parse_header gains two reads; emit_payload becomes dynamic)
```
parse_header2{b0; s, sender, topic, off, n. k[s; sender; topic; off; n]} ≡
  guard{ len(b0) ≥ 24;
    read_u32{ b0; 0; magic.
    guard{ magic = MAGIC;
      read_u32{ b0; 4; sender. read_u32{ b0; 8; topic.
      read_u32{ b0; 12; off.   read_u32{ b0; 16; n.
      advance{ b0; 12; s. k[s; sender; topic; off; n] } } } } };
      drop{ ERR_UNAUTHORIZED_OR_RATE_LIMITED } } };
    drop{ ERR_TRUNCATED_FRAME } }

emit_payload2{s; off; n; st} ≡                       (* s = b0 advanced by 12; off is ABSOLUTE in the frame *)
  guard{ 24 ≤ off ∧ off + n ≤ len(s) + 12;
    advance{ s; off − 12; p. take{ p; n; q. return{ (st, q) } } };
    drop{ ERR_BAD_PAYLOAD } }
```
check_rate_limit and verify_acl are I2's, unchanged.

## J3. The unfused term (B.1's order)
```
U2 ≡ parse_header2{ b0; s1, sender, topic, off, n.
       check_rate_limit{ bucket_st; sender; st'.
         verify_acl{ sender; topic;
           emit_payload2{ s1; off; n; st' } } } }
```

## J4. The fused target F2 (written by vir in A.3's style; it is NOT in the object, so it is an INPUT)
```
F2 ≡ guard{ len(b0) ≥ 24;
  read_u32{ b0; 0; magic. read_u32{ b0; 4; sender. read_u32{ b0; 8; topic.
  read_u32{ b0; 12; off.  read_u32{ b0; 16; n.
  guard{ magic = MAGIC ∧ can_access(sender, topic) ∧ has_tokens(bucket_st, sender);
    let_lin{ dec_tokens(bucket_st, sender); bucket_st'.
    guard{ 24 ≤ off ∧ off + n ≤ len(b0);
      advance{ b0; off; p. take{ p; n; q. return{ (bucket_st', q) } } };
      drop{ ERR_BAD_PAYLOAD } } };
    drop{ ERR_UNAUTHORIZED_OR_RATE_LIMITED } } } } } } };
  drop{ ERR_TRUNCATED_FRAME } }
```
Goal **J5: U2 ≡ F2**, scored as a rewrite chain (I7).
The new difficulty is that `slice_fuse` now yields `advance{b0; 12 + (off − 12); …}`. That equals `advance{b0; off; …}` only UNDER the enclosing guard's `24 ≤ off`, so the chain needs a rewrite whose side condition is discharged by a guard ABOVE it (a context-dependent rewrite). The bound `off + n ≤ len(s) + 12` likewise becomes `off + n ≤ len(b0)` only through the I1 slice law.
