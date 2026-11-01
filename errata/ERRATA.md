# Errata to the frozen object (O95)

The object (`../object/*.tex`) is never edited. Each defect gets a row here, with who found it and what each arm does about it.
An erratum states a DEFECT. It is not a repair. Whether a repaired form is used is decided per arm and recorded here,
and both arms get the same decision, or the comparison is not fair (brief, "same affordances").

| id | where | defect | found by | status |
|---|---|---|---|---|
| E1 | A.4 `BT %r8, ACL_BITMAP(%rip, %rcx, 8)` | NOT ENCODABLE: RIP-relative addressing takes no index register (SDM Vol. 2A §2.2.1.6). | paris @[bus] | OPEN. Blocks any machine arm on A.4; the spike must name its repaired form here before it starts. |
| E2 | A.4 `CMP $24,%rsi; JLT` | signed test (SF≠OF) on an unsigned length; needs JB. Differs for len ≥ 2^63. | paris | OPEN. Kept as a refinement-check target. |
| E3 | A.4 `SUB $1, BUCKET_ARR(…); JLT` | writes memory before the test; on drop_rate_limited the state is already decremented, while the A.3 term leaves it untouched. Not a refinement. | paris | OPEN. Kept as a refinement-check target. |
| E4 | A.4 ACL addressing | BT bit-string with stride rcx*8 reads another sender's row for topic ≥ 64: a hidden precondition topic < 64 (TopicId is U32 in A.1). | paris | OPEN. |
| E5 | A.4 `JMP emit_slice(%rax, %rdx)` | the exit is not an instruction (implied ABI) and drops the slice length (len−24); %rsi is never updated. | paris | OPEN. |
| E6 | A.3 / A.2 | the fused term uses `has_tokens`, `can_access`, `dec_tokens` and `len`, `∧` in atoms, none of which A.2's grammar declares (atoms are i · true · false · v · binop · relop). The Lean arm must add them as declared constants; that addition is recorded here, not in the object. | vir (first head) | OPEN. Same declaration list given to both arms. |
| E7 | A.3 | the derivation says it applies [beta_lin], [guard_merge], [slice_fuse], [dce_atom]; [read_comm] and [guard_true] / [const_fold] are stated but not named in the sequence, and B.1 (§5.2) has no `advance` nodes at all, so no `slice_fuse` redex exists until the inlined bodies of parse_header / check_rate_limit / verify_acl are given. Those bodies are NOT in the object. | vir (first head) | OPEN. The arms need the same inlined bodies; vir writes them ONCE as a separate input file (`../inputs/`), posted before either arm's first proof. |

E6–E7 are first-read notes by vir; each arm re-reads them and may dispute one on the bus.
