# Shared inputs for both arms (O95). Written ONCE by vir and identical for the Lean and MetaPRL arms

The frozen object (`../object/`) does not say enough to start a proof (errata E6, E7). This file supplies the missing parts.
It is an INPUT and not an erratum. It adds nothing that the object contradicts. Both arms get exactly these bytes.
An arm that needs anything else posts it on the bus for vir, and vir adds it here for BOTH arms, as a new commit.

## I1. Declared constants (E6)
Each one is an uninterpreted operator symbol of the VIR. An arm may give them a semantics only through the axioms listed here.
```
atoms   a ::= ... | len(a) | a1 ∧ a2 | has_tokens(a_st, a_p) | can_access(a_p, a_t)
lin ops     dec_tokens(st, p)                 (* the only let_lin op on bucket state *)
codes       ERR_TRUNCATED_FRAME · ERR_UNAUTHORIZED_OR_RATE_LIMITED   (* distinct drop codes *)
const       MAGIC = 0x4D534731   (A.1)
slice law   len(s) for  advance{b; i; s. …}  is  len(b) − i   (needs 0 ≤ i ≤ len(b))
read law    read_u32{s; j; v. …} on  advance{b; i; s. …}  reads b at i + j
```

## I2. The three spec bodies (E7), as HOAS terms with a continuation hole
Each spec is a second-order term in A.2's grammar. `k[...]` is the continuation (MetaPRL: a second-order variable. Lean: a function argument).
```
parse_header{b0; s, sender, topic. k[s; sender; topic]} ≡
  guard{ len(b0) ≥ 24;
    read_u32{ b0; 0; magic.
    guard{ magic = MAGIC;
      read_u32{ b0; 4; sender.
      read_u32{ b0; 8; topic.
      advance{ b0; 12; s. k[s; sender; topic] } } };
      drop{ ERR_UNAUTHORIZED_OR_RATE_LIMITED } } };
    drop{ ERR_TRUNCATED_FRAME } }

check_rate_limit{st; p; st'. k[st']} ≡
  guard{ has_tokens(st, p);
    let_lin{ dec_tokens(st, p); st'. k[st'] };
    drop{ ERR_UNAUTHORIZED_OR_RATE_LIMITED } }

verify_acl{p; t; k} ≡
  guard{ can_access(p, t); k; drop{ ERR_UNAUTHORIZED_OR_RATE_LIMITED } }

emit_payload{s; st} ≡ advance{ s; 12; payload. return{ (st, payload) } }
```

## I3. The unfused term (Exhibit B.1, in I2's notation; the order is B.1's: rate limit, then ACL)
```
U ≡ parse_header{ b0; s1, sender, topic.
      check_rate_limit{ bucket_st; sender; st'.
        verify_acl{ sender; topic;
          emit_payload{ s1; st' } } } }
```

## I4. The goal
Show `U ≡ F`, where F is the "Synthesized & Fused Single-Pass VIR Term" of A.3 (`object/appendix-A.tex`), as written, with `bucket_st'` for `st'`.
Equivalence is the arm's logic's equality of VIR terms (CTT: the rewrite judgment. Lean: equality of the denotation, or of the terms under a stated rewrite relation, and the arm says which).

## I5. The rule budget (what the predictions count)
GIVEN: the 4 A.2 rules (beta_lin, dce_atom, const_fold, guard_true) and the 3 A.3 rules (slice_fuse, guard_merge, read_comm), as written.
A step that needs ANY other rule (E8: the derivation needs commutations of advance, read_u32, guard and let_lin past one another, and
the reorder of the ACL guard before the rate-limit let_lin, none of which is stated) is an **AUX RULE**. The arm states it, proves it sound in its
logic (or declares it an axiom of the VIR, counted separately), and the harness counts it. Neither arm is told the other's aux rules.

## I6. The exit convention for A.4 (E5; paris's proposal @[bus], adopted for every machine arm)
OK exit: `%rax` = b0 + 24 (payload pointer), `%rsi` = len(b0) − 24 (payload length), `%rdx` = the bucket pointer, and memory equal except one bucket cell decremented.
Drop exits: the three labels drop_truncated · drop_unauthorized · drop_rate_limited. drop_unauthorized covers both the magic test and the ACL test, as in F's single error code. Memory is unchanged on every drop exit.
Precondition (E4): topic < 64. Buffer, ACL table, bucket array and code are pairwise disjoint.

## I7. What the SCORED I4 proof is (added 2026-11-01 00:4x, the same for both arms)
The scored proof of I4 is a REWRITE CHAIN: every step is one of the 7 given rules, a stated aux rule, or congruence under a binder (congruence is free and not counted).
A proof that reaches I4 by case-splitting on the guards' truth values, without the chain, is a SHORTCUT. It is recorded as a finding with its own counts and is never scored.
Why: mojave declared this rule for its arm at 00:12:23 (@[bus]), before any proof. The Lean arm had drafted a case-split proof (unbuilt) at that hour. A rule one arm keeps and the other does not is an unequal affordance, so vir, the owner of the inputs, makes it binding on both.
Declared conflict: vir learned the rule from the other arm's design post (a post addressed to vir as owner, not its proofs).
